/-
Release check for T2273 (dispatcher V1, Tue Oct  6 08:13 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §48, §50, §54, §56, §57 (1)-(2), §64 (4), §65, §66, §69 B, §88).
UN-21: the `Jak` half of the row `UNJakUywRow`: port of RBM2D `Universality/Jak.lean` (c9a24cf, 952 lines;
`jakRow` `:903`, private `Jak_main` `:834`, `Jak_fixed_time` `:553`, instances `JakCheck` `:923-948`) to the merged
band pins `UNJak`, `UNOUQUE`, `UNOUDiag`, `UNOUClaims`, `UNLocAvgBand` at `d ≥ 3`, the merged UN-19/UN-20 layers
(`measure_bad_le_of_queBadMat`, `jakGridGood`, `jak_pointwise_good`, `jak_pointwise_crude`) and the exponent
`c' = 𝔠𝔡/30` of the merged row (`Pins.lean:805-809`; RBM2D `𝔠/36`); new file `RBM3D/Universality/Jak.lean`.
The merged pin `UNJak` is TRUE as stated at `c' = 𝔠𝔡/30`, `C = 3 nf + 16`: no primed successor.  No primed name
occurs here.
Section 1: the merged names the new file builds on.
Section 2: the statements of the theorems of T2273 as `def T2273_<name> : Prop` (2.1 helper, 2.2 targets,
2.3 instances); the library states the theorem `<name>` (namespace `RBM.Univ`; instances in
`RBM.Univ.JakInst`) with exactly this body (binder names may be added).
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2273-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4; namespace `RBM.Univ`)
#check @RBM.Univ.stieltjesN           -- :88
#check @RBM.Univ.UNModel.band         -- :116
#check @RBM.Univ.ouTStar              -- :142
#check @RBM.Univ.ouP                  -- :145
#check @RBM.Univ.ouMat                -- :150
#check @RBM.Univ.ouMat_isHermitian    -- :154
#check @RBM.Univ.Nsz                  -- :372
#check @RBM.Univ.queBound             -- :384
#check @RBM.Univ.queBadMat            -- :392
#check @RBM.Univ.UNLocAvgBand         -- :416 (owed; first hypothesis of the row, unused)
#check @RBM.Univ.InWindow             -- :501
#check @RBM.Univ.scirc                -- :612
#check @RBM.Univ.UNOUQUE              -- :637 (`queBadMat … (𝔡 / 3) (𝔡 / 6) E a`, bound `queBound W 𝔡 (𝔡/3) (𝔡/6) τQ`)
#check @RBM.Univ.UNOUDiag             -- :648 (`N^ε < ‖Gres … (E + i N^{-1+2τU}) true x x‖`, `|E| ≤ 2 - κ`)
#check @RBM.Univ.UNOUClaims           -- :659 (not registered; see the ticket, Registry)
#check @RBM.Univ.UNJak                -- :694 (the pin proved in row form)
#check @RBM.Univ.UNJakUywRow          -- :805 (owed; stays owed: UN-23)
#check @RBM.Univ.UNClaimRow           -- :815 (consumer shape, `c' = 𝔠 * 𝔡 / 30`)
#check @RBM.Univ.un_que_exponent      -- :894 (`-(min (2(𝔡/3)) (2𝔡/5)) + 2(𝔡/6) = -(𝔡/15)`)
#check @RBM.Univ.un_window_sub        -- :908
#check @RBM.Univ.un_W_neg_le          -- :929 (`W^{-x} ≤ N^{-(𝔠x)}` from `N^𝔠 ≤ W`)
#check @RBM.Univ.un_cprime            -- :940 (`min (𝔠𝔡/6) (𝔠(𝔡/15 - 𝔡/30)) = 𝔠𝔡/30`)
#check @RBM.Univ.UNBadY               -- :1147
#check @RBM.Univ.unBadY_measure_le    -- :1320
#check @RBM.Univ.un_const_absorb      -- :1346
#check @RBM.Univ.UNInst.sz0_adm       -- :1518
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0): band bridge (not a target here)
#check @RBM.Univ.UNJakk_band          -- :540
#check @RBM.Univ.UNOUClaimsk_band     -- :556
-- UN-02a (`Universality/OU.lean`, T2177, a52eb85)
#check @RBM.Univ.isProbabilityMeasure_ouP   -- :44 (instance)
-- UN-19 (`Universality/JakSpectral.lean`, T2251, 88183b6)
#check @RBM.Univ.siteBlock                    -- :220
#check @RBM.Univ.blockM                       -- :227
#check @RBM.Univ.unBadY_of_blockM             -- :545
#check @RBM.Univ.measure_bad_le_of_queBadMat  -- :559 (`(2d+1) p`, window `N⁻¹ W^{𝔡/3}`, threshold `W^{-𝔡/6}`)
-- UN-20 (`Universality/JakKernel.lean`, T2267, c77e68c)
#check @RBM.Univ.im_Gres_apply_self   -- :48
#check @RBM.Univ.jakGridGood          -- :167
#check @RBM.Univ.jak_pointwise_good   -- :854
#check @RBM.Univ.jak_pointwise_crude  -- :933
-- MD-1 (`Defs/Sizes.lean`, T2006, 0a873f1; namespace `RBM.Gauss`)
#check @RBM.Gauss.Sizes.three_le_L    -- :145
#check @RBM.Gauss.Sizes.W_pos         -- :146
#check @RBM.Gauss.Sizes.size          -- :157
#check @RBM.Gauss.Sizes.WO            -- :164 (`W^{-d/2+𝔡} ≤ lam ∧ lam ≤ 𝔡⁻¹`, eventually)
#check @RBM.Gauss.Sizes.Bandwidth     -- :168 (`N^𝔠 ≤ W`, eventually)
#check @RBM.Gauss.Sizes.SizeTendsto   -- :173
#check @RBM.Gauss.Sizes.Admissible    -- :177 (`0 < 𝔠 ∧ 0 < 𝔡 ∧ SizeTendsto ∧ Bandwidth 𝔠 ∧ WO 𝔡`)
#check @RBM.Gauss.SizesInst.sz0       -- :260
#check @RBM.Gauss.SizesInst.sz0_admissible  -- :331
-- MD-3 (`Loop/GLoopFlow.lean`, T2013, 868b3b4)
#check @RBM.Gauss.Gres                -- :74

namespace T2273Check

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Univ

/-! ## 2. Statements -/

/-! ### 2.1 Helper (public): `𝔠𝔡 ≤ 1/2` from admissibility (RBM2D private `Jak_c_le_half` `:471`, `c ≤ 1/2`).
`𝔠 < 1/d` from `N^𝔠 ≤ W`, `W^d < N`, `N → ∞`; `𝔡 ≤ d/2` from `(eq:WO)` (`W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`)
and `W ≥ N^𝔠 → ∞`. -/

def T2273_un_cd_le_half : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → 𝔠 * 𝔡 ≤ 1 / 2

/-! ### 2.2 Targets -/

/-- Target 1 (public form of RBM2D private `Jak_main` `:834`): `UNJak` at `c' = 𝔠𝔡/30`, `C = 3 nf + 16`,
for one `τ_U ∈ (0, 1/4]`, from the two `𝐇_t` claims at that `τ_U`. -/
def T2273_unJak_of_ouClaims : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUE sz 𝔡 τU → UNOUDiag sz τU →
        UNJak sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30)

/-- Target 2 (RBM2D `jakRow` `:903`): the `Jak` half of `UNJakUywRow` (`Pins.lean:805-809`), same hypotheses
and quantifiers, `C = 3 nf + 16`, `τ₀ = min τ₁ (1/4)`. -/
def T2273_jakRow : Prop :=
  UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNJak sz E nf τU C (𝔠 * 𝔡 / 30)

/-! ### 2.3 Instances (namespace `RBM.Univ.JakInst`; RBM2D `JakCheck` `:923-948`): `sz0` (`d = 3`,
`𝔠 = 1/6`, `𝔡 = 1/10`), `κ = 1/2`, `E = 1`, `nf = 2`; the window is non-empty at every size. -/

def T2273_inst_row : Prop :=
  UNLocAvgBand → UNOUClaims →
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNJak SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30)

def T2273_inst_window : Prop :=
  ∀ (n : ℕ) (τU : ℝ), 0 < τU →
    InWindow SizesInst.sz0 1 1 τU n (⟨1, (Nsz SizesInst.sz0 n)⁻¹⟩ : ℂ) ∧
      0 ≤ ouTStar SizesInst.sz0 τU n

/-! ## 3. Downstream shapes (information, not targets) -/

-- UN-23 (`Uyw`, `jakUywRow`) pairs target 2 with `uywRow` into `UNJakUywRow` (`Pins.lean:805`, conjunction at the
-- same `C`, `τ₀`: take `max` of the two `C` and `min` of the two `τ₀`; `UNJak` is monotone in `C` only through
-- `N ≥ 1`, which is UN-23's to prove); UN-24 (`claimRow`) consumes `C = 3 nf + 16` through `UNClaimRow` (`:815`).
example : Prop := UNJakUywRow
example : Prop := UNClaimRow

end T2273Check
