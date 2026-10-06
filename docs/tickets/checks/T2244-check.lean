/-
Release check for T2244 (dispatcher V1, Tue Oct  6 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 (O2),
§50, §54, §56, §57 (1), §64 (4), §66, §69 B).
UN-09: the GUE local law from the Schur tail, the deterministic bootstrap: port of RBM2D
`Universality/GUELocalBootstrap.lean` (c9a24cf; `schurErr` `:176`, `sc_one_step` `:230`, `chain_bound` `:355`,
`schurBud` `:446`, `glPts` `:513`, `GlSmall` `:729`, `gue_local_det` `:743`, `glSmall_eventually` `:850`,
`GUESchurTail` `:908`, `GUELocal_of_tail` `:944`) to `Sizes d`, `Ω d L W`, `N = (W L)^d`; new file
`RBM3D/Universality/GUELocalBootstrap.lean`.  Proves `UNGUESchurTail → UNGUELocal` (the merged owed pin
`UNGUELocal`, `Pins.lean:489`, unchanged); the new pin `UNGUESchurTail` is owed (UN-10).
The prime is the ASCII `'` of `main`.
Section 1: the merged names the new file builds on; Mathlib names of the route.
Section 2: the new vocabulary (2.1, bodies to be copied verbatim into namespace `RBM.Univ`), the statements of the
theorems of T2244 as `def T2244_<name> : Prop` (2.2-2.5), the instances (2.6); the library states the theorem
`<name>` (namespace in the docstring) with exactly this body (binder names may be added to hypotheses).
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2244-check.lean`.
-/
import RBM3D
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4)
#check @RBM.Univ.gueP                 -- :67
#check @RBM.Univ.isProbabilityMeasure_gueP  -- :70
#check @RBM.Univ.stieltjesN           -- :88 (through `Gres M z true`, not `green`)
#check @RBM.Univ.Nsz                  -- :372
#check @RBM.Univ.UNGUELocal           -- :489 (owed; the target of `un_gueLocal_of_tail`)
-- UN-11 (`Universality/Step1RegularityGUE.lean`, T2220, merged e9ef940)
#check @RBM.Univ.Step1RegularityGUEInst.inst_sz0_size_tendsto  -- :947
-- the semicircle (`Defs/Semicircle.lean`, fbc9870; namespace `RBM`)
#check @RBM.msc                       -- :116
#check @RBM.msc_mul                   -- :118
#check @RBM.msc_im_pos                -- :123
#check @RBM.norm_msc_lt_one           -- :152
-- resolvents
#check @RBM.green                     -- `Green/EntryCore.lean:34` (890a89f)
#check @RBM.Gauss.Gres                -- `Loop/GLoopFlow.lean:74` (868b3b4)
#check @RBM.Gauss.norm_Gsig_le_inv_eta  -- `Gauss/FlowCalculus.lean:644` (6f99812; replaces RBM2D `norm_green_le`)
#check @RBM.green_sub_green           -- `Induction/ConArgDet.lean:73` (bbd22a5; RBM2D `Hierarchy/WardResolvent`)
#check @RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero  -- `Induction/ConArgDet.lean:380` (bbd22a5)
#check @RBM.Ind.norm_apply_le_l2_opNorm  -- `Induction/Split.lean:670` (aa42e43)
#check @RBM.Green.green_diag_ne_zero  -- `Green/LDE.lean:503` (7c7652e)
-- the model (T2006, 0a873f1)
#check @RBM.Gauss.Idx                 -- `Defs/Sizes.lean:46`
#check @RBM.Gauss.Sizes               -- `Defs/Sizes.lean:138`
#check @RBM.Gauss.Sizes.size          -- `Defs/Sizes.lean:157`
#check @RBM.Gauss.Sizes.card_Idx      -- `Defs/Sizes.lean:160`
#check @RBM.Gauss.Sizes.three_le_L    -- `Defs/Sizes.lean:145`
#check @RBM.Gauss.Sizes.W_pos         -- `Defs/Sizes.lean:146`
#check @RBM.Gauss.SizesInst.sz0       -- `Defs/Sizes.lean:260`
#check @RBM.Gauss.SizesInst.card_Idx_sz0  -- `Defs/Sizes.lean:368` (`N = 2097152` at `n = 0`)
#check @RBM.Gauss.Ω                   -- `Gauss/FineModel.lean:84`
#check @RBM.Gauss.Xmat                -- `Gauss/FineModel.lean:113`
#check @RBM.Gauss.Xmat_isHermitian    -- `Gauss/FineModel.lean:142`
-- Mathlib
#check @tendsto_natCast_atTop_atTop
#check @Real.rpow_le_rpow_of_exponent_le
#check @Matrix.nonsing_inv_eq_ringInverse

namespace RBM.Univ.T2244Check

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`) -/

/-- The Schur error `Υ_i(z) = (G_ii)⁻¹ + z + m_N(z)` (RBM2D `:176`; `green` is `RBM.green`, `stieltjesN` the merged
one through `Gres`). -/
noncomputable def schurErr {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) (i : ι) : ℂ :=
  (green H z i i)⁻¹ + z + stieltjesN H z

/-- The bulk gap `√(κ (4 - κ))` (RBM2D `:341`). -/
noncomputable def cGap (κ : ℝ) : ℝ := Real.sqrt (κ * (4 - κ))

/-- The Schur-error budget `N^ε (N^{-1/2} + (2/(N Im z))^{1/2} + (N Im z)⁻¹)` (RBM2D `:446`). -/
noncomputable def schurBud (N ε : ℝ) (z : ℂ) : ℝ :=
  N ^ ε * (1 / Real.sqrt N + Real.sqrt (2 / (N * z.im)) + 1 / (N * z.im))

/-- The simplified budget `6 N^ε / √(N η)` (RBM2D `:450`). -/
noncomputable def budSimp (N ε η : ℝ) : ℝ := 6 * N ^ ε / Real.sqrt (N * η)

/-- The grid mesh `N⁻⁴` (RBM2D `:500`). -/
noncomputable def glMesh (N : ℝ) : ℝ := (N ^ 4)⁻¹

/-- Number of steps in the real direction (RBM2D `:503`). -/
noncomputable def glJ (N κ : ℝ) : ℕ := ⌊2 * (2 - κ) / glMesh N⌋₊

/-- Number of steps in the imaginary direction (RBM2D `:506`). -/
noncomputable def glK (N τ : ℝ) : ℕ := ⌊(10 - N ^ (-1 + τ)) / glMesh N⌋₊

/-- (RBM2D `:508`) -/
noncomputable def glE (N κ : ℝ) (j : ℕ) : ℝ := -(2 - κ) + j * glMesh N

/-- (RBM2D `:510`) -/
noncomputable def glEta (N : ℝ) (k : ℕ) : ℝ := 10 - k * glMesh N

/-- The grid points `E_j + i η_k` of the window (RBM2D `:513`). -/
noncomputable def glPts (N κ τ : ℝ) : Finset ℂ :=
  ((Finset.range (glJ N κ + 1)) ×ˢ (Finset.range (glK N τ + 1))).image
    (fun p => (⟨glE N κ p.1, glEta N p.2⟩ : ℂ))

/-- The smallness conditions of the bootstrap (RBM2D `structure GlSmall` `:729`; here a conjunction in the same
order `N55, h1, h2, h3`; the library may use the RBM2D `structure` with these four fields instead, say so). -/
def GlSmall (N κ τ : ℝ) : Prop :=
  55 ≤ N ∧ 6 * N ^ (-(τ / 4)) ≤ 1 / 4 ∧
    24 * N ^ (-(τ / 4)) / cGap κ + 2 * N ^ (-(τ / 4)) ≤ min (cGap κ / 2) (1 / 4) ∧
    24 * N ^ (τ / 4) / cGap κ + 13 ≤ N ^ τ

/-- **Pin `UNGUESchurTail`** (new; registry class **owed**, UN-10 `GUELocalSchur`; RBM2D `GUESchurTail` `:908`): for
the `N × N` GUE, `N = (W L)^d`, and every deterministic set `Γ_n` of at most `N^q` points of the window
`|Re z| ≤ 2 - κ`, `N^{-1+τ} ≤ Im z ≤ 10`, with probability `≥ 1 - N^{-D}` simultaneously for all `z ∈ Γ_n` and all
rows `i`: `|Υ_i(z)| ≤ schurBud N ε z` whenever `Im m_N(z) ≤ 2`.  Dimension-free (only `N`). -/
def UNGUESchurTail : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
  ∀ κ τ ε D : ℝ, 0 < κ → 0 < τ → 0 < ε → 0 < D → ∀ q : ℕ, ∀ Γ : ℕ → Finset ℂ,
    (∀ n, ∀ z ∈ Γ n, |z.re| ≤ 2 - κ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10) →
    (∀ᶠ n in atTop, (((Γ n).card : ℕ) : ℝ) ≤ Nsz sz n ^ q) →
    ∀ᶠ n in atTop, gueP d (sz.L n) (sz.W n)
        {ω | ∃ z ∈ Γ n, ∃ i : Idx d (sz.L n) (sz.W n),
          (stieltjesN (Xmat d (sz.L n) (sz.W n) ω) z).im ≤ 2 ∧
            schurBud (Nsz sz n) ε z < ‖schurErr (Xmat d (sz.L n) (sz.W n) ω) z i‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-! ### 2.2 Target 1: facts on `msc` (RBM2D `:73-171`; pure `ℂ`, no model) -/

/-- `norm_msc_add_z_gt_one` (namespace `RBM.Univ`; RBM2D `:78`). -/
def T2244_norm_msc_add_z_gt_one : Prop := ∀ {z : ℂ}, 0 < z.im → 1 < ‖msc z + z‖

/-- `im_le_norm_msc_add_z` (RBM2D `:93`). -/
def T2244_im_le_norm_msc_add_z : Prop := ∀ {z : ℂ}, 0 < z.im → z.im ≤ ‖msc z + z‖

/-- `norm_msc_le_inv_im` (RBM2D `:98`). -/
def T2244_norm_msc_le_inv_im : Prop := ∀ {z : ℂ}, 0 < z.im → ‖msc z‖ ≤ (z.im)⁻¹

/-- `msc_disc_sq` (RBM2D `:108`). -/
def T2244_msc_disc_sq : Prop := ∀ z : ℂ, (2 * msc z + z) ^ 2 = z ^ 2 - 4

/-- `sqrt_le_norm_two_msc_add_z` (RBM2D `:114`): the bulk gap. -/
def T2244_sqrt_le_norm_two_msc_add_z : Prop :=
  ∀ {z : ℂ} {κ : ℝ}, 0 < κ → |z.re| ≤ 2 - κ → Real.sqrt (κ * (4 - κ)) ≤ ‖2 * msc z + z‖

/-- `im_le_norm_two_msc_add_z` (RBM2D `:141`). -/
def T2244_im_le_norm_two_msc_add_z : Prop := ∀ {z : ℂ}, 0 < z.im → z.im ≤ ‖2 * msc z + z‖

/-- `sc_stability` (RBM2D `:152`). -/
def T2244_sc_stability : Prop :=
  ∀ {m z : ℂ} {c Λ : ℝ}, 0 < c → c ≤ ‖2 * msc z + z‖ → ‖m * (z + m) + 1‖ ≤ Λ → ‖m - msc z‖ ≤ c / 2 →
    ‖m - msc z‖ ≤ 2 * Λ / c

/-- `norm_msc_sub_le` (RBM2D `:261`). -/
def T2244_norm_msc_sub_le : Prop :=
  ∀ {z z' : ℂ}, 0 < z.im → 0 < z'.im → ‖msc z - msc z'‖ ≤ ‖z - z'‖ / (z.im * z'.im)

/-! ### 2.3 Target 2: the self-consistent equation and the a priori bounds (RBM2D `:173-340`; generic `ι`) -/

/-- `sc_residual` (RBM2D `:180`). -/
def T2244_sc_residual : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ {z : ℂ}, z.im ≠ 0 →
    stieltjesN H z * (z + stieltjesN H z) + 1 = (Fintype.card ι : ℂ)⁻¹ * ∑ i, schurErr H z i * green H z i i

/-- `norm_green_diag_le_two` (RBM2D `:198`). -/
def T2244_norm_green_diag_le_two : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ {z : ℂ}, 0 < z.im →
    ∀ i : ι, ‖schurErr H z i‖ ≤ 1 / 4 → ‖stieltjesN H z - msc z‖ ≤ 1 / 4 → ‖green H z i i‖ ≤ 2

/-- `sc_one_step` (RBM2D `:230`). -/
def T2244_sc_one_step : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ {z : ℂ}, 0 < z.im →
    ∀ {c υ : ℝ}, 0 < c → c ≤ ‖2 * msc z + z‖ → υ ≤ 1 / 4 → (∀ i, ‖schurErr H z i‖ ≤ υ) →
      ‖stieltjesN H z - msc z‖ ≤ min (c / 2) (1 / 4) → ‖stieltjesN H z - msc z‖ ≤ 4 * υ / c

/-- `norm_stieltjesN_le` (RBM2D `:293`). -/
def T2244_norm_stieltjesN_le : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ {z : ℂ}, 0 < z.im →
    ‖stieltjesN H z‖ ≤ (z.im)⁻¹

/-- `norm_stieltjesN_sub_le` (RBM2D `:311`): the Lipschitz bound used by the grid lift. -/
def T2244_norm_stieltjesN_sub_le : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ {z z' : ℂ},
    0 < z.im → 0 < z'.im → ‖stieltjesN H z - stieltjesN H z'‖ ≤ ‖z - z'‖ / (z.im * z'.im)

/-! ### 2.4 Target 3: the chain, the budget, the grid, the deterministic law (RBM2D `:341-884`) -/

/-- `chain_bound` (RBM2D `:355`): the bootstrap down a vertical line. -/
def T2244_chain_bound : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {H : Matrix ι ι ℂ}, H.IsHermitian →
    ∀ {κ : ℝ}, 0 < κ → κ ≤ 2 → ∀ {x : ℝ}, |x| ≤ 2 - κ → ∀ {h : ℝ}, 0 < h → ∀ {K : ℕ} {η : ℕ → ℝ},
      (∀ k, η k = 10 - k * h) → (∀ k ≤ K, 0 < η k) → ∀ {υ : ℕ → ℝ}, (∀ k ≤ K, υ k ≤ 1 / 4) →
        (∀ k ≤ K, ∀ i, (stieltjesN H ⟨x, η k⟩).im ≤ 2 → ‖schurErr H ⟨x, η k⟩ i‖ ≤ υ k) →
        (∀ k, k + 1 ≤ K → 4 * υ k / cGap κ + 2 * h / (η k * η (k + 1)) ≤ min (cGap κ / 2) (1 / 4)) →
          ∀ k ≤ K, ‖stieltjesN H ⟨x, η k⟩ - msc ⟨x, η k⟩‖ ≤ 4 * υ k / cGap κ

/-- `schurBud_le` (RBM2D `:452`). -/
def T2244_schurBud_le : Prop :=
  ∀ {N ε : ℝ}, 1 ≤ N → ∀ {z : ℂ}, 1 ≤ N * z.im → z.im ≤ 10 → schurBud N ε z ≤ budSimp N ε z.im

/-- `exists_glPt` (RBM2D `:543`). -/
def T2244_exists_glPt : Prop :=
  ∀ {N κ τ : ℝ}, 0 < N → ∀ {z : ℂ}, |z.re| ≤ 2 - κ → N ^ (-1 + τ) ≤ z.im → z.im ≤ 10 →
    ∃ j k : ℕ, j ≤ glJ N κ ∧ k ≤ glK N τ ∧ 0 ≤ z.re - glE N κ j ∧
      z.re - glE N κ j ≤ glMesh N ∧ 0 ≤ glEta N k - z.im ∧ glEta N k - z.im ≤ glMesh N

/-- `interp_le` (RBM2D `:642`). -/
def T2244_interp_le : Prop :=
  ∀ {N τ η : ℝ}, 1 ≤ N → 0 < τ → N ^ (-1 + τ) ≤ η → η ≤ 10 → 4 * glMesh N / (η * η) ≤ 13 / Real.sqrt (N * η)

/-- `card_glPts_le` (RBM2D `:681`). -/
def T2244_card_glPts_le : Prop :=
  ∀ {N κ τ : ℝ}, 55 ≤ N → 0 < κ → κ ≤ 2 → τ ≤ 1 → ((glPts N κ τ).card : ℝ) ≤ N ^ 9

/-- `gue_local_det` (RBM2D `:743`): the deterministic law on the whole window from the grid. -/
def T2244_gue_local_det : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ {κ τ N : ℝ},
    0 < κ → κ ≤ 2 → 0 < τ → τ ≤ 1 / 2 → GlSmall N κ τ →
      (∀ z ∈ glPts N κ τ, ∀ i, (stieltjesN H z).im ≤ 2 → ‖schurErr H z i‖ ≤ schurBud N (τ / 4) z) →
        ∀ z : ℂ, |z.re| ≤ 2 - κ → N ^ (-1 + τ) ≤ z.im → z.im ≤ 10 →
          ‖stieltjesN H z - msc z‖ ≤ N ^ τ / Real.sqrt (N * z.im)

/-- `glSmall_eventually` (RBM2D `:850`). -/
def T2244_glSmall_eventually : Prop :=
  ∀ {κ τ : ℝ}, 0 < κ → κ ≤ 2 → 0 < τ → ∀ {N : ℕ → ℝ}, Tendsto N atTop atTop → ∀ᶠ n in atTop, GlSmall (N n) κ τ

/-! ### 2.5 Target 4: the assembly (RBM2D `:885-984`) -/

/-- `glPts_mem` (namespace `RBM.Univ`; RBM2D `:920`). -/
def T2244_glPts_mem : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {κ τ : ℝ}, κ ≤ 2 → τ ≤ 1 → ∀ n : ℕ,
    ∀ z ∈ glPts (Nsz sz n) κ τ, |z.re| ≤ 2 - κ ∧ Nsz sz n ^ (-1 + τ) ≤ z.im ∧ z.im ≤ 10

/-- `glPts_card` (RBM2D `:937`). -/
def T2244_glPts_card : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), Tendsto (fun n => sz.size n) atTop atTop → ∀ {κ τ : ℝ}, 0 < κ → κ ≤ 2 → τ ≤ 1 →
    ∀ᶠ n in atTop, (((glPts (Nsz sz n) κ τ).card : ℕ) : ℝ) ≤ Nsz sz n ^ 9

/-- **`un_gueLocal_of_tail`** (namespace `RBM.Univ`; RBM2D `GUELocal_of_tail` `:944`): the merged owed pin
`UNGUELocal` from the new owed pin `UNGUESchurTail`. -/
def T2244_un_gueLocal_of_tail : Prop := UNGUESchurTail → UNGUELocal

/-! ### 2.6 Instances (namespace `RBM.Univ.GUELocalBootstrapInst`; `d = 3`, `sz0`, `κ = 1`, `τ = 1/10`) -/

/-- `inst_schurTail`: `UNGUESchurTail` at `sz0`, `κ = 1`, `τ = 1/10`, `ε = 1/40`, `D = 2`, `q = 9`, `Γ_n` the grid
(membership by `glPts_mem`, cardinality by `glPts_card`). -/
def T2244_inst_schurTail : Prop :=
  UNGUESchurTail →
    ∀ᶠ n in atTop, gueP 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n)
      {ω | ∃ z ∈ glPts (Nsz RBM.Gauss.SizesInst.sz0 n) 1 (1 / 10),
        ∃ i : Idx 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n),
          (stieltjesN (Xmat 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n) ω) z).im ≤ 2 ∧
            schurBud (Nsz RBM.Gauss.SizesInst.sz0 n) (1 / 40) z <
              ‖schurErr (Xmat 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n) ω) z i‖} ≤
      ENNReal.ofReal (Nsz RBM.Gauss.SizesInst.sz0 n ^ (-(2 : ℝ)))

/-- `inst_grid_nonempty`: the grid at `n = 0` of `sz0` (`N = 2097152`) is nonempty (the pin is not vacuous). -/
def T2244_inst_grid_nonempty : Prop := (glPts (2097152 : ℝ) 1 (1 / 10)).Nonempty

/-- `inst_glSmall`: the smallness conditions hold eventually along `sz0`. -/
def T2244_inst_glSmall : Prop := ∀ᶠ n in atTop, GlSmall (Nsz RBM.Gauss.SizesInst.sz0 n) 1 (1 / 10)

/-- `inst_gueLocal`: `un_gueLocal_of_tail` at `sz0`, `κ = 1`, `τ = 1/10`, `D = 2`. -/
def T2244_inst_gueLocal : Prop :=
  UNGUESchurTail →
    ∀ᶠ n in atTop, gueP 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n)
      {ω | ∃ z : ℂ, |z.re| ≤ 2 - 1 ∧ Nsz RBM.Gauss.SizesInst.sz0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 10 ∧
          Nsz RBM.Gauss.SizesInst.sz0 n ^ (1 / 10 : ℝ) / Real.sqrt (Nsz RBM.Gauss.SizesInst.sz0 n * z.im) <
            ‖stieltjesN (Xmat 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.W n) ω) z - msc z‖} ≤
      ENNReal.ofReal (Nsz RBM.Gauss.SizesInst.sz0 n ^ (-(2 : ℝ)))

/-- `inst_glSmall_witness` (deterministic nonvacuity of `gue_local_det`): the hypothesis `GlSmall` is not
contradictory, it holds at a concrete `N` (`N = 10^80`, `κ = 1`, `τ = 1/10`: `N^{τ/4} = 100`, h1 `0.06 ≤ 0.25`,
h2 `0.159 ≤ 0.25`, h3 `1398.6 ≤ 10^8`; RBM2D docstring: from `N ≈ 10^73`). -/
def T2244_inst_glSmall_witness : Prop := GlSmall ((10 : ℝ) ^ (80 : ℕ)) 1 (1 / 10)

/-! ## 3. Downstream shapes (not targets of T2244; information) -/

/-- UN-10 closes `UNGUELocal`: with `un_gueSchurTail : UNGUESchurTail` (UN-10, `GUELocalSchur`), the composition
`un_gueLocal_of_tail un_gueSchurTail : UNGUELocal` removes the hypothesis `UNGUELocal` from `un_infty1Row'`
(`GUETranslation`, T2226), `un_core_of_rows'`, `un_bUniv_of_rows'` (`PinsDens.lean:220, 233`) and BA's
`baBUniv_of_rows` (T2241). -/
def T2244_D_gueLocal : Prop := UNGUESchurTail → UNGUELocal

/-- The band chain after T2244 (as `T2226_D_un_bUniv`, with `UNGUELocal` replaced by its new source). -/
def T2244_D_un_bUniv : Prop :=
  UNUnivMainRow → UNClaimRow → UNEMCTE2Row → UNJakUywRow → UNOURow → UNDensBandRow → UNTrLocalBandRow →
    UNNormBandRow → UNL32 → (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNGUESchurTail → UNGreenCorrAll →
      UNBUniv

end RBM.Univ.T2244Check
