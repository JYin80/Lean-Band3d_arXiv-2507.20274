/-
T2276 (UN-51a, `Universality/ZeroModeProfile`) — step-0 check file.  Pins only: imports of merged
modules, `#check` of merged names, vocabulary `def`s, `def … : Prop` pin texts, Prop-valued
`example`s.  No proof, no `sorry`, no `by`.  Must compile on `main` (ed29a8b) as is.
-/
import RBM3D.Universality.OU
import RBM3D.Universality.OUHessian
import RBM3D.Endpoints
import RBM3D.Propagator.Prop6Hold
import RBM3D.Propagator.Prop5Hold
import RBM3D.Main.QUEFromQDiff
import RBM3D.Green.IBP
import RBM3D.Induction.Split

open MeasureTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints
open scoped NNReal ENNReal

/-! ## 1. Merged names used (every one `#check`ed with its full namespace) -/

-- `RBM3D/Universality/Pins.lean` (f8ad4b4)
#check @RBM.Univ.UNModel.band          -- :116
#check @RBM.Univ.ouTStar               -- :142
#check @RBM.Univ.ouP                   -- :145
#check @RBM.Univ.ouMat                 -- :150
#check @RBM.Univ.ouMat_isHermitian     -- :154
#check @RBM.Univ.ouMat_zero            -- :160
#check @RBM.Univ.Nsz                   -- :372
#check @RBM.Univ.queBadMat             -- :392
#check @RBM.Univ.queBound              -- :384
#check @RBM.Univ.UNQueBand             -- :404
#check @RBM.Univ.UNLocAvgBand          -- :416
#check @RBM.Univ.UNMLOut               -- :432
#check @RBM.Univ.UNOUQUE               -- :637
#check @RBM.Univ.UNOUDiag              -- :648
#check @RBM.Univ.UNOUClaims            -- :659
#check @RBM.Univ.UNOURow               -- :793
#check @RBM.Univ.un_claimAll_of_rows   -- :849 (consumer of `UNOURow`)
-- `RBM3D/Universality/OU.lean` (a52eb85)
#check @RBM.Univ.ouVar                 -- :56
#check @RBM.Univ.measurable_ouMat      -- :80
#check @RBM.Univ.ouSample_law          -- :208
#check @RBM.Univ.ouMat_zero_map        -- :233
-- `RBM3D/Propagator/Basic.lean` (020ec7a), `RBM3D/Defs/Block.lean` (a722f63)
#check @RBM.Theta                      -- Basic :70
#check @RBM.Theta_mul                  -- :82
#check @RBM.mul_Theta                  -- :86
#check @RBM.eq_Theta_of_mul            -- :92
#check @RBM.Theta_apply_add_right      -- :154
#check @RBM.one_sub_ne_zero            -- :178
#check @RBM.Theta0                     -- :225
#check @RBM.Theta0_apply               -- :229
#check @RBM.SB                         -- Block :44
#check @RBM.SB_transpose               -- :58
#check @RBM.SB_apply_add_right         -- :62
#check @RBM.sum_SB_row                 -- :108
#check @RBM.norm_SB                    -- :136 (`Matrix.Norms.Operator`, ℓ^∞ operator norm)
-- `RBM3D/Propagator/Pins.lean` (b06ff9b), `Prop5Hold.lean` (f40d8ca), `Prop6Hold.lean` (6cc5032)
#check @RBM.PropSpin                   -- Pins :30
#check @RBM.Prop8ZeroMode              -- Pins :87
#check @RBM.prop8ZeroMode_holds        -- Prop5Hold :1266
#check @RBM.prop5to8_holds             -- Prop6Hold :433
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.msc                        -- :116
#check @RBM.norm_msc_lt_one            -- :152
#check @RBM.norm_msc_pos               -- :198
#check @RBM.lemT                       -- :193
#check @RBM.lemT_pos                   -- :204
#check @RBM.lemT_lt_one                -- :209
#check @RBM.mE_lemE                    -- :238
#check @RBM.mE_im                      -- :42
#check @RBM.norm_mE                    -- :63
#check @RBM.lemma28_quant              -- :359
#check @RBM.zdistD                     -- Lattice :71
-- `RBM3D/Gauss/FineModel.lean`, `RBM3D/Defs/Sizes.lean` (0a873f1), `Green/IBP.lean` (382b6d9), `Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.svarF                -- :47
#check @RBM.Gauss.svarF_nonneg         -- :51
#check @RBM.Gauss.svarF_comm           -- :54
#check @RBM.Gauss.split                -- Sizes :64
#check @RBM.Gauss.Iblk                 -- Sizes :92
#check @RBM.Gauss.card_Idx             -- Sizes :107
#check @RBM.Gauss.Sizes.Admissible     -- Sizes :177
#check @RBM.Gauss.Sizes.neZeroL        -- Sizes :152
#check @RBM.Gauss.Sizes.neZeroW        -- Sizes :153
#check @RBM.Gauss.SizesInst.sz0        -- Sizes :260
#check @RBM.Green.IBP_sum_svarF_row    -- IBP :1205
#check @RBM.Gauss.Gres                 -- GLoopFlow :74
-- `RBM3D/Endpoints.lean` (8a43715), `Main/QUECore.lean` (389ad9e), `Main/QUEFromQDiff.lean` (d822fd7)
#check @RBM.Endpoints.avg2             -- :75
#check @RBM.Endpoints.ThetaPM          -- :80
#check @RBM.Endpoints.ThetaPP          -- :84
#check @RBM.Endpoints.profPM           -- :88
#check @RBM.Endpoints.profPP           -- :92
#check @RBM.Endpoints.qdBoundExp       -- :101
#check @RBM.Endpoints.QDiff            -- :197
#check @RBM.Endpoints.MAThetaDiff      -- QUECore :76 (template of target 2.4)
#check @RBM.Endpoints.thetaDiff        -- QUECore :105 (template; not imported by the target)
#check @RBM.Endpoints.etaQ             -- QUEFromQDiff :85 (`ouEtaQ sz 𝔡 n` is `etaQ sz n (𝔡 / 3)` by unfolding)
#check @RBM.Endpoints.queRowDiff       -- QUEFromQDiff :244 (consumer-side template, UN-52)

namespace RBM.Univ.T2276Check

/-! ## 2. Vocabulary (target section 1; copied verbatim into `RBM.Univ`) -/

/-! ### 2.1 the profile and `Θ̃` -/

/-- `ζ(t) = 1 - e^{-t}` (RBM2D `ouZeta`). -/
noncomputable def ouZeta (t : ℝ) : ℝ := 1 - Real.exp (-t)

/-- `S̃_{xy} = (1 - ζ) S_{xy} + ζ N⁻¹`, `S = svarF d L W lam`, `N = (W L)^d`. -/
noncomputable def Stilde (d L W : ℕ) [NeZero L] [NeZero W] (lam ζ : ℝ) (i j : Idx d L W) : ℝ :=
  (1 - ζ) * svarF d L W lam i j + ζ / (((W * L) ^ d : ℕ) : ℝ)

/-- The all-ones matrix `J` on `Z_L^d`. -/
noncomputable def Jmat (d L : ℕ) : Matrix (Zd d L) (Zd d L) ℂ := Matrix.of fun _ _ => 1

/-- `S̃^(B) = (1 - ζ) S^(B)(lam) + (ζ / L^d) J`. -/
noncomputable def SBtilde (d L : ℕ) (lam ζ : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  ((((1 - ζ : ℝ)) : ℂ)) • SB d L lam + ((ζ : ℂ) / (L : ℂ) ^ d) • Jmat d L

/-- `Θ̃_ξ = (1 - ξ S̃^(B))⁻¹` (`Ring.inverse`, as the merged `RBM.Theta`). -/
noncomputable def ThetaTilde (d L : ℕ) [NeZero L] (lam ζ : ℝ) (ξ : ℂ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  Ring.inverse (1 - ξ • SBtilde d L lam ζ)

/-- The two spectral parameters of the profiles: `m²` (`σ = true`), `|m|²` (`σ = false`). -/
noncomputable def xiQ (z : ℂ) (σ : Bool) : ℂ :=
  if σ then msc z ^ 2 else (((‖msc z‖ ^ 2 : ℝ)) : ℂ)

/-! ### 2.2 the layer constants and the profiles with `Θ̃` -/

/-- Design value of the layer's `τ_U` bound at `d ≥ 3` (T2276b): `min(𝔠/12, 𝔠𝔡/12, 1/100)`. -/
noncomputable def ouTauMax (𝔠 𝔡 : ℝ) : ℝ := min (min (𝔠 / 12) (𝔠 * 𝔡 / 12)) (1 / 100)

/-- The scale of `UNOUDiag`/`UNOULL`: `η = N^{-1+2τ_U}` (token-equal to `Pins.lean:654`). -/
noncomputable def ouEtaLL {d : ℕ} (sz : Sizes d) (τU : ℝ) (n : ℕ) : ℝ := Nsz sz n ^ (-1 + 2 * τU)

/-- The QUE scale of `UNOUQUE` (`ε₀ = 𝔡/3`): `η_Q = W^{-𝔡/3} lam W^{d/2} / N` (= `etaQ sz n (𝔡/3)`). -/
noncomputable def ouEtaQ {d : ℕ} (sz : Sizes d) (𝔡 : ℝ) (n : ℕ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n)

/-- `profPM` with `Θ` replaced by `Θ̃` at `ζ`. -/
noncomputable def profPMTilde {d : ℕ} (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * ThetaTilde d (sz.L n) (sz.lam n) ζ (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b /
    ((sz.W n : ℕ) : ℂ) ^ d

/-- `profPP` with `Θ` replaced by `Θ̃` at `ζ`. -/
noncomputable def profPPTilde {d : ℕ} (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  msc z ^ 2 * ThetaTilde d (sz.L n) (sz.lam n) ζ (msc z ^ 2) a b / ((sz.W n : ℕ) : ℂ) ^ d

/-! ## 3. Pins of the interface (target section 4; new `Prop`s, registered owed where assumed) -/

/-- **`UNOULL`**: per-sequence moment form of the weak local law for `𝐇_t` at `η = N^{-1+2τ_U}`. -/
def UNOULL {d : ℕ} (sz : Sizes d) (τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ δ : ℝ, 0 < δ → ∀ p : ℕ,
      ∀ᶠ n in atTop, ∀ x : Idx d (sz.L n) (sz.W n),
        ∫ ω, ‖Gres (ouMat (UNModel.band sz) n (t n) ω)
            ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
          ∂(ouP (UNModel.band sz) n) ≤ Nsz sz n ^ δ

/-- **`UNOUEq747`**: the expectation half of `(eq:diffu1)`/`(eq:diffu2)` (`QDiff`, `Endpoints.lean:197-210`) for
`𝐇_t` at the QUE scale `z_n = E_n + i η_Q`, with `Θ̃` at `ζ(t_n)`, per sequence. -/
def UNOUEq747 {d : ℕ} (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ : ℝ, 0 < τ →
      ∀ᶠ n in atTop, ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMat (UNModel.band sz) n (t n) ω)
              ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPMTilde sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
        ‖(∫ ω, avg2 sz n (fun x y =>
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
              Gres (ouMat (UNModel.band sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
            ∂(ouP (UNModel.band sz) n)) -
          profPPTilde sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n)

/-- **Row `UNG1Row`** (UN-51, `RandomLayerB` `g1Row`): the two layer pins from the inputs of `UNOURow`. -/
def UNG1Row : Prop :=
  (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOULL sz τU ∧ UNOUEq747 sz 𝔡 τU

/-- **Row `UNG2bRow`** (UN-52, `QUEFlow` `g2bRow`): `UNOUQUE` for `𝐇_t` from `UNOUEq747`. -/
def UNG2bRow : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → UNOUEq747 sz 𝔡 τU → UNOUQUE sz 𝔡 τU

/-! ## 4. Target statements (each target's statement is the body of `T2276_<name>`) -/

/-! ### 4.1 profile (§1) -/

def T2276_Stilde_zero : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (i j : Idx d L W),
    Stilde d L W lam 0 i j = svarF d L W lam i j

def T2276_sum_Stilde_row : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ), 3 ≤ L → ∀ (ζ : ℝ) (i : Idx d L W),
    ∑ j, Stilde d L W lam ζ i j = 1

def T2276_ouVar_eq_Stilde : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam t : ℝ), 0 ≤ t → ∀ c : CoordF d L W,
    (ouVar d L W lam t c : ℝ) =
      if c.1 = c.2.1 then Stilde d L W lam (ouZeta t) c.1 c.2.1
      else Stilde d L W lam (ouZeta t) c.1 c.2.1 / 2

def T2276_Stilde_eq_SBtilde_mul : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam ζ : ℝ) (i j : Idx d L W),
    (Stilde d L W lam ζ i j : ℂ) =
      SBtilde d L lam ζ (split d L W i).1 (split d L W j).1 * (((W : ℂ) ^ d)⁻¹)

/-! ### 4.2 `Θ̃` (§2) -/

def T2276_ThetaTilde_zero : Prop :=
  ∀ (d L : ℕ) [NeZero L] (lam : ℝ) (ξ : ℂ), ThetaTilde d L lam 0 ξ = Theta d L lam ξ

def T2276_ThetaTilde_eq : Prop :=
  ∀ (d L : ℕ) [NeZero L] (lam : ℝ), 3 ≤ L → ∀ {ξ : ℂ}, ‖ξ‖ < 1 → ∀ {ζ : ℝ}, 0 ≤ ζ → ζ ≤ 1 →
    ThetaTilde d L lam ζ ξ = Theta d L lam (ξ * (1 - (ζ : ℂ))) +
      (ξ * ζ / ((L : ℂ) ^ d * (1 - ξ * (1 - (ζ : ℂ))) * (1 - ξ))) • Jmat d L

/-- **The `d ≥ 3` oscillation bound of `Θ̃`** (replaces RBM2D `norm_ThetaTilde_sub_le`, `90 (1 + log L)`):
uniform in `L`, `ζ ∈ [0,1]`, `z` in the bulk, constant `C(d, 𝔡, κ)`, no `log L`. -/
def T2276_norm_ThetaTilde_sub_le : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ lam : ℝ, 0 < lam → lam ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
        ∀ (σ : Bool) (u v : Zd d L),
          ‖ThetaTilde d L lam ζ (xiQ z σ) u v - ThetaTilde d L lam ζ (xiQ z σ) 0 0‖ ≤ C * (lam ^ 2)⁻¹

/-- Consumer form (UN-52, as `queRowDiff`): row differences of the `Θ̃` profiles. -/
def T2276_profTilde_rowDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
        ∀ a b b' : Zd d (sz.L n),
          ‖profPMTilde sz n ζ z a b - profPMTilde sz n ζ z a b'‖ ≤
              C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
          ‖profPPTilde sz n ζ z a b - profPPTilde sz n ζ z a b'‖ ≤
              C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d

def T2276_profPMTilde_zero : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)),
    profPMTilde sz n 0 z a b = profPM sz n z a b ∧ profPPTilde sz n 0 z a b = profPP sz n z a b

/-! ### 4.3 constants (§3) -/

def T2276_ouTauMax_pos : Prop := ∀ {𝔠 𝔡 : ℝ}, 0 < 𝔠 → 0 < 𝔡 → 0 < ouTauMax 𝔠 𝔡

def T2276_ouTauMax_slack : Prop :=
  ∀ {𝔠 𝔡 τU : ℝ}, 0 < 𝔠 → 0 < 𝔡 → τU ≤ ouTauMax 𝔠 𝔡 →
    12 * τU ≤ 𝔠 ∧ 12 * τU ≤ 𝔠 * 𝔡 ∧ τU < 𝔠 * 𝔡 ∧ 3 * τU / 2 < 2 * (𝔠 * 𝔡) / 3

/-! ### 4.4 assembly (§5, §6) -/

def T2276_ouDiag_of_ouLL : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} {τU : ℝ}, UNOULL sz τU → UNOUDiag sz τU

def T2276_ouRow_of_pins : Prop := UNG1Row → UNG2bRow → UNOURow

/-! ## 5. Prop-valued examples (shapes only; no proof obligation) -/

example : Prop := T2276_norm_ThetaTilde_sub_le
example : Prop := T2276_ouRow_of_pins
example : Prop := UNOULL RBM.Gauss.SizesInst.sz0 (1 / 100)
example : Prop := UNOUEq747 RBM.Gauss.SizesInst.sz0 (1 / 10) (1 / 100)
example : Prop := UNOUDiag RBM.Gauss.SizesInst.sz0 (1 / 100)
example : Prop := UNG1Row → UNG2bRow → UNOURow

end RBM.Univ.T2276Check
