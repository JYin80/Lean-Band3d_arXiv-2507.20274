/-
Release check for T2280 (dispatcher V1, Tue Oct  6 09:50 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §48, §50, §54, §56, §57 (1)-(2), §64 (4), §65, §66, §69 B, §90, §91).
UN-23: the `Uyw` half of the row `UNJakUywRow` and the row itself: port of RBM2D `Universality/Uyw.lean` (c9a24cf,
1021 lines; `uywRow` `:914`, private `Uyw_main` `:845`, `Uyw_fixed_time` `:553`, `jakUywRow` `:951`, instances
`UywCheck` `:972-1016`) to the merged band pins `UNUyw`, `UNOUQUE`, `UNOUDiag`, `UNOUClaims`, `UNLocAvgBand`,
`UNJakUywRow` at `d ≥ 3`, the merged UN-22 pair layer (`blockM2`, `measure_bad2_le_of_queBadMat`,
`uyw_pointwise_good`, `uyw_pointwise_crude`), the merged UN-21 `Jak` half (`unJak_of_ouClaims`, `jakRow`,
`un_cd_le_half`) and the exponent `c' = 𝔠𝔡/30` of the merged row (`Pins.lean:805-809`; RBM2D `𝔠/36`); new file
`RBM3D/Universality/Uyw.lean`.
The merged pin `UNUyw` is TRUE as stated at `c' = 𝔠𝔡/30`, `C = 3 nf + 16`, `τ₀ = min τ₁ (1/4)`: no primed
successor.  No primed name occurs here.
Section 1: the merged names the new file builds on.
Section 2: the statements of the public theorems of T2280 as `def T2280_<name> : Prop` (2.1 targets,
2.2 instances); the library states the theorem `<name>` (namespace `RBM.Univ`; instances in
`RBM.Univ.UywInst`) with exactly this body (binder names may be added).
Section 3: the private intermediate statements of the exponent redo (`Uyw_<name>`, private in the library; the
library may generalise `Ω : Type` to `Type*` and add binder names, nothing else).
Section 4: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2280-check.lean`.
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
#check @RBM.Univ.UNOUQUE              -- :637 (owed; `queBadMat … (𝔡 / 3) (𝔡 / 6) E a`, bound `queBound W 𝔡 (𝔡/3) (𝔡/6) τQ`)
#check @RBM.Univ.UNOUDiag             -- :648 (proved from `UNOULL` by `ouDiag_of_ouLL`, T2276)
#check @RBM.Univ.UNOUClaims           -- :659 (owed, T2273)
#check @RBM.Univ.UNJak                -- :694 (proved in row form by T2273)
#check @RBM.Univ.UNUyw                -- :708 (target; integrand `:712-716`)
#check @RBM.Univ.UNJakUywRow          -- :805 (target)
#check @RBM.Univ.UNClaimRow           -- :815 (consumer shape, `c' = 𝔠 * 𝔡 / 30`)
#check @RBM.Univ.un_claimAll_of_rows  -- :849 (consumer: premise `rJ : UNJakUywRow`)
#check @RBM.Univ.un_bUniv_of_rows     -- :866 (consumer: premise `rJ : UNJakUywRow`)
#check @RBM.Univ.un_que_exponent      -- :894
#check @RBM.Univ.un_window_sub        -- :908
#check @RBM.Univ.un_W_neg_le          -- :929 (`W^{-x} ≤ N^{-(𝔠x)}` from `N^𝔠 ≤ W`)
#check @RBM.Univ.un_cprime            -- :940 (`min (𝔠𝔡/6) (𝔠(𝔡/15 - 𝔡/30)) = 𝔠𝔡/30`)
#check @RBM.Univ.UNInst.sz0_adm       -- :1518
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0): band bridges (not targets)
#check @RBM.Univ.UNUywk_band          -- :546
#check @RBM.Univ.UNJakUywRowk_band    -- :569
-- UN-02a (`Universality/OU.lean`, T2177, a52eb85)
#check @RBM.Univ.isProbabilityMeasure_ouP   -- :44 (instance)
-- UN-19 (`Universality/JakSpectral.lean`, T2251, 88183b6)
#check @RBM.Univ.siteBlock            -- :220
#check @RBM.Univ.blockM               -- :227
-- UN-20 (`Universality/JakKernel.lean`, T2267, c77e68c)
#check @RBM.Univ.im_Gres_apply_self   -- :48
#check @RBM.Univ.jakGridGood          -- :167
-- UN-22 (`Universality/UywKernel.lean`, T2271, ed29a8b)
#check @RBM.Univ.blockM2                          -- :800
#check @RBM.Univ.blockM2_self                     -- :808
#check @RBM.Univ.blockM2_eq                       -- :837
#check @RBM.Univ.green_spectral_identity_blockM2  -- :941
#check @RBM.Univ.measure_bad2_le_of_queBadMat     -- :1061 (`(2d+1) p`, window `N⁻¹ W^{𝔡/3}`, threshold `W^{-𝔡/6}`)
#check @RBM.Univ.uyw_pointwise_good               -- :1179
#check @RBM.Univ.uyw_pointwise_crude              -- :1254
-- UN-21 (`Universality/Jak.lean`, T2273, 803bb88)
#check @RBM.Univ.un_cd_le_half        -- :451 (`𝔠𝔡 ≤ 1/2`)
#check @RBM.Univ.unJak_of_ouClaims    -- :854 (`UNJak … (3nf+16) (𝔠𝔡/30)`)
#check @RBM.Univ.jakRow               -- :931
#check @RBM.Univ.JakInst.inst_row     -- :954
#check @RBM.Univ.JakInst.inst_window  -- :962
#check @RBM.Univ.JakInst.inst_unJak   -- :983
-- UN-51a (`Universality/ZeroModeProfile.lean`, T2276, 66cddb4): information only
#check @RBM.Univ.UNOULL
#check @RBM.Univ.ouDiag_of_ouLL       -- :641
-- MD-1 (`Defs/Sizes.lean`, T2006, 0a873f1; namespace `RBM.Gauss`)
#check @RBM.Gauss.Sizes.three_le_L    -- :145
#check @RBM.Gauss.Sizes.W_pos         -- :146
#check @RBM.Gauss.Sizes.size          -- :157
#check @RBM.Gauss.Sizes.WO            -- :164
#check @RBM.Gauss.Sizes.Bandwidth     -- :168
#check @RBM.Gauss.Sizes.SizeTendsto   -- :173
#check @RBM.Gauss.Sizes.Admissible    -- :177
#check @RBM.Gauss.SizesInst.sz0       -- :260
#check @RBM.Gauss.SizesInst.sz0_admissible  -- :331
-- MD-3 (`Loop/GLoopFlow.lean`, T2013, 868b3b4)
#check @RBM.Gauss.Gres                -- :74

namespace T2280Check

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Univ

/-! ## 2. Statements -/

/-! ### 2.1 Targets -/

/-- Target 1 (public form of RBM2D private `Uyw_main` `:845`): `UNUyw` at `c' = 𝔠𝔡/30`, `C = 3 nf + 16`,
for one `τ_U ∈ (0, 1/4]`, from the two `𝐇_t` claims at that `τ_U` (as `unJak_of_ouClaims`, `Jak.lean:854`). -/
def T2280_unUyw_of_ouClaims : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUE sz 𝔡 τU → UNOUDiag sz τU →
        UNUyw sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30)

/-- Target 2 (RBM2D `uywRow` `:914`): the `Uyw` half of `UNJakUywRow` (`Pins.lean:805-809`), same hypotheses and
quantifiers as `jakRow` (`Jak.lean:931`), `C = 3 nf + 16`, `τ₀ = min τ₁ (1/4)`. -/
def T2280_uywRow : Prop :=
  UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
      ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)

/-- Target 3 (RBM2D `jakUywRow` `:951`): the merged row, verbatim. -/
def T2280_jakUywRow : Prop := UNJakUywRow

/-! ### 2.2 Instances (namespace `RBM.Univ.UywInst`; RBM2D `UywCheck` `:972-1016`): `sz0` (`d = 3`, `𝔠 = 1/6`,
`𝔡 = 1/10`), `κ = 1/2`, `E = 1`, `nf = 2`; the window holds two distinct energies at every size. -/

def T2280_inst_row : Prop :=
  UNLocAvgBand → UNOUClaims →
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNJak SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) ∧
        UNUyw SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30)

def T2280_inst_uywRow : Prop :=
  UNLocAvgBand → UNOUClaims →
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
      UNUyw SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30)

def T2280_inst_unUyw : Prop :=
  ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
    UNOUQUE SizesInst.sz0 (1 / 10) τU → UNOUDiag SizesInst.sz0 τU →
      UNUyw SizesInst.sz0 1 2 τU (3 * ((2 : ℕ) : ℝ) + 16) ((1 / 6 : ℝ) * (1 / 10) / 30)

def T2280_inst_window : Prop :=
  ∀ (n : ℕ) (τU : ℝ), 0 < τU →
    ∃ z : Fin 2 → ℂ, (∀ i, InWindow SizesInst.sz0 1 1 τU n (z i)) ∧ z 0 ≠ z 1 ∧
      (0 : Fin 2) ≠ 1 ∧ 0 ≤ ouTStar SizesInst.sz0 τU n

/-! ## 3. Private intermediate statements (the exponent redo; private `Uyw_<name>` in the library) -/

/-- RBM2D `Uyw_o_le` `:118` with `c ≤ 1/2` weakened to `c ≤ 1` (`c = 2𝔠𝔡 ≤ 1` from `un_cd_le_half`; the proof
only needs `1 - c/6 + 2τ + δ ≥ 0`). -/
def T2280_Uyw_o_le : Prop :=
  ∀ (X c τ δ κ ηt w' : ℝ) (K' : ℕ), 1 ≤ X → 0 < c → c ≤ 1 → 0 < τ → 0 ≤ δ → 0 < κ →
    ηt = X ^ (-1 + 2 * τ) → w' = (2 * X ^ (1 - c / 6))⁻¹ → κ / 4 < 2 ^ (K' + 1) * w' →
      X ^ δ * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹ ≤
        (48 + 64 / κ ^ 2) * X ^ (1 - c / 6 + 2 * τ + δ)

/-- RBM2D `Uyw_good_total_le` `:213` redone (template: merged `Jak_good_total_le`, `Jak.lean:213`): good-event
exponent `c/36` (`= 𝔠𝔡/18` at `c = 2𝔠𝔡`), bad probability `K N^{-c'}` (`K = 2d+1`, RBM2D `5 N^{-c/18}`), pin
exponent `c' ≤ c/36`, slack `2 (C₁ + 4K) ≤ N^{6τ}` (RBM2D `2 (C₁ + 20)`). -/
def T2280_Uyw_good_total_le : Prop :=
  ∀ (X c c' τ δ C₁ K : ℝ) (sc m : ℕ), 1 ≤ X → c' ≤ c / 36 → 0 < τ → 0 ≤ δ → 0 ≤ C₁ → 0 ≤ K →
    sc ≤ m → ((m : ℝ) + 3) * δ ≤ τ → 2 * (C₁ + 4 * K) ≤ X ^ (6 * τ) →
      X ^ ((3 * τ + δ) * (sc : ℝ)) * (X⁻¹ * (C₁ * X ^ (3 - c / 36 + 8 * τ + 2 * δ))) +
          X ^ ((3 * τ + δ) * (sc : ℝ)) * (X⁻¹ * (4 * X ^ (3 + 8 * τ + 2 * δ))) *
            (K * X ^ (-c')) ≤
        1 / 2 * X ^ (2 - c' + (3 * (sc : ℝ) + 16) * τ)

/-- RBM2D `Uyw_crude_total_le` `:264` at the pin exponent `c'` (RBM2D `c/36`, `c < 36`). -/
def T2280_Uyw_crude_total_le : Prop :=
  ∀ (X c' τ D : ℝ) (sc m : ℕ), 1 ≤ X → 0 < τ → c' ≤ 2 → sc ≤ m →
    (1 + τ) * ((m : ℝ) + 4) + 3 ≤ D → 16 * (4 + (m : ℝ)) ≤ X →
      4 * X ^ ((1 + τ) * ((sc : ℝ) + 4)) * (((4 + (m : ℝ)) * X) * ((2 * X) * X ^ (-D))) ≤
        1 / 2 * X ^ (2 - c' + (3 * (sc : ℝ) + 16) * τ)

/-- Private copy of the merged private `Jak_queBound_eq` (`Jak.lean:546`). -/
def T2280_Uyw_queBound_eq : Prop :=
  ∀ (W : ℕ) (𝔡 : ℝ), 0 < 𝔡 →
    queBound W 𝔡 (𝔡 / 3) (𝔡 / 6) (𝔡 / 30) = ENNReal.ofReal ((W : ℝ) ^ (-(𝔡 / 30)))

/-- RBM2D `Uyw_fixed_time` `:553` in the shape of the merged `Jak_fixed_time` (`Jak.lean:561`): one random
Hermitian matrix `Hr` on a probability space, `X = N = (W L)^d`, `c = 2𝔠𝔡`; `hdiag` = `UNOUDiag` at the grid
energies, `hque` = `UNOUQUE` at `τ_Q = 𝔡/30` after `Uyw_queBound_eq`; RBM2D `h5` with `20 = 4·5` replaced by
`4(2d+1)`; the integrand is the integrand of `UNUyw` (`Pins.lean:712-716`) at `Hr ω = ouMat … t ω`, `u₁ = z i`,
`u₂ = z j`, `lam = sz.lam n`. -/
def T2280_Uyw_fixed_time : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ),
    (∀ ω, (Hr ω).IsHermitian) →
    ∀ {X 𝔠 𝔡 c κ τ δ C₀ E D : ℝ} {m : ℕ},
    (((W * L) ^ d : ℕ) : ℝ) = X → X ^ 𝔠 ≤ (W : ℝ) →
    0 < 𝔠 → 0 < 𝔡 → c = 2 * (𝔠 * 𝔡) → 𝔠 * 𝔡 ≤ 1 / 2 →
    (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam →
    0 < κ → κ ≤ 2 → 0 < τ → 0 < δ →
    ((m : ℝ) + 3) * δ ≤ τ → (1 + τ) * ((m : ℝ) + 4) + 3 ≤ D →
    |E| ≤ 2 - κ → 16 * (4 + (m : ℝ)) ≤ X → 2 * C₀ ≤ X ^ (c / 6) →
    C₀ / X + 2 * X ^ (-1 + 2 * τ) < κ / 4 → X ^ (-1 + c / 6) < κ / 2 →
    2 * ((193 + 256 / κ ^ 2) + 4 * ((2 * d + 1 : ℕ) : ℝ)) ≤ X ^ (6 * τ) →
    (∀ e : ℝ, |e| < 2 - κ / 2 →
      P {ω | ∃ x : Idx d L W, X ^ δ <
        ‖Gres (Hr ω) ((e : ℂ) + ((X ^ (-1 + 2 * τ) : ℝ) : ℂ) * Complex.I) true x x‖} ≤
        ENNReal.ofReal (X ^ (-D))) →
    (∀ b : Zd d L,
      P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤
        ENNReal.ofReal ((W : ℝ) ^ (-(𝔡 / 30)))) →
    ∀ (s : Finset (Fin m)) (w : Fin m → ℂ) (u₁ u₂ : ℂ),
    (∀ i, |(w i).re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ (w i).im ∧ (w i).im ≤ X ^ (-1 + τ)) →
    (|u₁.re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ u₁.im ∧ u₁.im ≤ X ^ (-1 + τ)) →
    (|u₂.re - E| ≤ C₀ / X ∧ X ^ (-1 - τ) ≤ u₂.im ∧ u₂.im ≤ X ^ (-1 + τ)) →
    ∀ (y : Idx d L W) (b₁ b₂ : Bool),
      ∫ ω, (∏ j ∈ s, (stieltjesN (Hr ω) (w j)).im) *
          ‖∑ x, (Gres (Hr ω) u₁ b₁ * Gres (Hr ω) u₁ b₁) x y * scirc d L W lam x y *
              (Gres (Hr ω) u₂ b₂ * Gres (Hr ω) u₂ b₂) y x‖ ∂P ≤
        X ^ (2 - 𝔠 * 𝔡 / 30 + (3 * (s.card : ℝ) + 16) * τ)

/-! ## 4. Downstream shapes (information, not targets) -/

-- `UNJakUywRow` is a premise of the merged `un_claimAll_of_rows` (`Pins.lean:849`), `un_bUniv_of_rows` (`:866`),
-- `PinsDens.lean:234, :599`, `Pins.lean:1757, :1797` (`UNInst`); target 3 discharges it.  UN-24 (`UnivMain`: `claimRow`
-- proves `UNClaimRow` (`:815`), `univMainRow` proves `UNUnivMainRow` (`:745`)) does not import `Uyw` (§91 (1));
-- `UNUnivMainRow` reads `UNClaimAll`, not `UNJakUywRow`.  The model-generic `UNJakUywRowk` stays owed
-- (`UNJakUywRowk_band` is the band bridge).
example : Prop := UNClaimRow
example : Prop := UNUnivMainRow
example : Prop := T2280_jakUywRow ∧ T2280_uywRow ∧ T2280_unUyw_of_ouClaims

end T2280Check
