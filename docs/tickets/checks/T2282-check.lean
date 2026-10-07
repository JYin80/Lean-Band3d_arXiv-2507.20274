/-
T2282 (UN-51g, `Universality/OUInterfaceK`) — step-0 check file.  Pins only: imports of merged
modules, `#check` of merged names, one `structure` (vocabulary), vocabulary `def`s, `def … : Prop`
pin texts, Prop-valued `example`s.  No proof, no `sorry`, no `by`.  Must compile on `main` (66cddb4) as is.
The imports of `RBM3D.Main.QUEFromQDiff` and `RBM3D.BA.UNPins` are for `#check`s and the BA shape
example only; the target file imports neither (layering: no `Universality` file imports `Main` or `BA`).
-/
import RBM3D.Universality.ZeroModeProfile
import RBM3D.Universality.PinsK
import RBM3D.Main.QUEFromQDiff
import RBM3D.BA.UNPins

open MeasureTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints
open scoped NNReal ENNReal

/-! ## 1. Merged names used (every one `#check`ed with its full namespace) -/

-- `RBM3D/Universality/Pins.lean` (f8ad4b4)
#check @RBM.Univ.UNModel               -- :104
#check @RBM.Univ.UNModel.band          -- :116
#check @RBM.Univ.ouTStar               -- :142
#check @RBM.Univ.ouP                   -- :145
#check @RBM.Univ.ouMat                 -- :150
#check @RBM.Univ.Nsz                   -- :372
#check @RBM.Univ.queBound              -- :384
#check @RBM.Univ.queBadMat             -- :392
#check @RBM.Univ.UNQueBand             -- :404
#check @RBM.Univ.UNLocAvgBand          -- :416
#check @RBM.Univ.UNMLOut               -- :432
#check @RBM.Univ.UNOUQUE               -- :637
#check @RBM.Univ.UNOUDiag              -- :648
#check @RBM.Univ.UNOUClaims            -- :659
#check @RBM.Univ.UNOURow               -- :793
-- `RBM3D/Universality/OU.lean` (a52eb85)
#check @RBM.Univ.isProbabilityMeasure_ouP  -- :44 (instance)
#check @RBM.Univ.measurable_ouMat      -- :80
-- `RBM3D/Universality/PinsK.lean` (fdbb6f0)
#check @RBM.Univ.UNModelC              -- :55
#check @RBM.Univ.UNModel.toC           -- :61
#check @RBM.Univ.ouMatC                -- :69
#check @RBM.Univ.ouMatC_isHermitian    -- :79
#check @RBM.Univ.ouMatC_eq_ouMat_add   -- :100
#check @RBM.Univ.unPinsK_toC_toUNModel -- :110
#check @RBM.Univ.ouMatC_toC            -- :119
#check @RBM.Univ.UNKind                -- :307 (fields `M`, `lamV`, `bulk`, `mdet`; no profile, no new field: §57 (1))
#check @RBM.Univ.UNKind.band           -- :315
#check @RBM.Univ.UNOUQUEk              -- :326
#check @RBM.Univ.UNOUDiagk             -- :335
#check @RBM.Univ.UNOUClaimsk           -- :421
#check @RBM.Univ.UNOURowk              -- :426
#check @RBM.Univ.un_claimAll_of_rowsk  -- :454 (consumer of `UNOURowk`)
#check @RBM.Univ.unPinsK_band_bulk     -- :517
#check @RBM.Univ.unPinsK_band_M        -- :520
#check @RBM.Univ.UNOUQUEk_band         -- :522 (the pattern of the band bridges)
#check @RBM.Univ.UNOUDiagk_band        -- :528
#check @RBM.Univ.UNOURowk_band         -- :560
-- `RBM3D/Universality/ZeroModeProfile.lean` (66cddb4)
#check @RBM.Univ.ouZeta                -- :55
#check @RBM.Univ.ouTauMax              -- :78
#check @RBM.Univ.ouEtaLL               -- :81
#check @RBM.Univ.ouEtaQ                -- :84
#check @RBM.Univ.profPMTilde           -- :88
#check @RBM.Univ.profPPTilde           -- :93
#check @RBM.Univ.UNOULL                -- :97
#check @RBM.Univ.UNOUEq747             -- :107
#check @RBM.Univ.UNG1Row               -- :126
#check @RBM.Univ.UNG2bRow              -- :132
#check @RBM.Univ.profTilde_rowDiff     -- :469
#check @RBM.Univ.ouTauMax_pos          -- :530
#check @RBM.Univ.ouDiag_of_ouLL        -- :641 (template of `ouDiagk_of_ouLLk`; its private helpers :547, :583, :596 are copied)
#check @RBM.Univ.ouRow_of_pins         -- :719 (template of `ouRowk_of_pins`)
-- `RBM3D/Endpoints.lean` (8a43715), `RBM3D/Main/QUEFromQDiff.lean` (d822fd7; consumer templates, not imported by the target)
#check @RBM.Endpoints.calB             -- :58
#check @RBM.Endpoints.avg2             -- :75
#check @RBM.Endpoints.qdBoundExp       -- :101
#check @RBM.Endpoints.etaQ             -- QUEFromQDiff :85
#check @RBM.Endpoints.queFixed         -- QUEFromQDiff :285
#check @RBM.Endpoints.queChain         -- QUEFromQDiff :463
#check @RBM.Endpoints.QUE_of_QDiff     -- QUEFromQDiff :502
-- `RBM3D/Defs/Sizes.lean` (0a873f1), `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `RBM3D/Induction/Split.lean` (aa42e43)
#check @RBM.Gauss.Sizes.Admissible     -- :177
#check @RBM.Gauss.Sizes.card_Idx       -- :160
#check @RBM.Gauss.SizesInst.sz0        -- :260
#check @RBM.Gauss.Gres                 -- GLoopFlow :74
#check @RBM.Ind.norm_apply_le_l2_opNorm -- Split :670
-- `RBM3D/BA/UNPins.lean` (88d7676; information: the BA consumer; not imported by the target)
#check @RBM.Univ.UNModelC.ba           -- :64
#check @RBM.Univ.UNKind.ba             -- :84
#check @RBM.Univ.UNQueBA               -- :99
#check @RBM.Univ.UNLocAvgBA            -- :103
#check @RBM.Univ.UNMLOutBA             -- :110
#check @RBM.Univ.UNOURowBA             -- :123 (`UNOURowk` at `UNKind.ba`)

namespace RBM.Univ.T2282Check

/-! ## 2. Vocabulary (target §1; copied verbatim into `RBM.Univ`) -/

/-- **The OU-layer profile of a kind** (T-class data, supplied by the kind's twin: band
`UNOUProfile.band` from `ZeroModeProfile`; block Anderson: BA-C3 `BA/GUEEntry`).  `pm sz n ζ z a b`
and `pp sz n ζ z a b` are the two-loop profiles `|m|² Θ̃^{(+,-)}_{ab}/W^d`, `m² Θ̃^{(+,+)}_{ab}/W^d`
of `𝐇_t` at `ζ = ζ(t)` (`S̃ = (1 - ζ) S + ζ N⁻¹ J`).  The kind `K` is a phantom index: it records
which model the profile belongs to ("two data, one model", DECISIONS §66 (5)). -/
structure UNOUProfile {d : ℕ} (K : UNKind d) where
  pm : ∀ sz : Sizes d, ∀ n : ℕ, ℝ → ℂ → Zd d (sz.L n) → Zd d (sz.L n) → ℂ
  pp : ∀ sz : Sizes d, ∀ n : ℕ, ℝ → ℂ → Zd d (sz.L n) → Zd d (sz.L n) → ℂ

/-- The band profile: `profPMTilde`, `profPPTilde` (T2276, `ZeroModeProfile.lean:88, 93`). -/
noncomputable def UNOUProfile.band (d : ℕ) : UNOUProfile (UNKind.band d) where
  pm := fun sz n ζ z a b => profPMTilde sz n ζ z a b
  pp := fun sz n ζ z a b => profPPTilde sz n ζ z a b

/-! ## 3. Pins of the generic interface (target §2; new `Prop`s) -/

/-- **`UNOUProfRowk`** (T-class; band: `profTilde_rowDiff` verbatim, BA: BA-C3): row differences of
the profile, `C lam⁻² W^{-d}` with `C = C(d, 𝔡, κ)`, uniformly in `ζ ∈ [0,1]` and `z` in the kind's bulk. -/
def UNOUProfRowk {d : ℕ} (K : UNKind d) (P : UNOUProfile K) : Prop :=
  ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → K.bulk sz κ z.re n → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
        ∀ a b b' : Zd d (sz.L n),
          ‖P.pm sz n ζ z a b - P.pm sz n ζ z a b'‖ ≤
              C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
          ‖P.pp sz n ζ z a b - P.pp sz n ζ z a b'‖ ≤
              C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d

/-- **`UNOULLk`**: `UNOULL` for the kind `K` (carrier `ouMatC (K.M sz)`, law `ouP (K.M sz).toUNModel`);
the bulk condition sits inside `∀ᶠ n` (for every energy sequence, eventually: if `E n` is in the
bulk at `n`, the moment bound holds), so that a kind whose bulk is empty at some `n` is not vacuous. -/
def UNOULLk {d : ℕ} (K : UNKind d) (sz : Sizes d) (τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ,
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ δ : ℝ, 0 < δ → ∀ p : ℕ,
      ∀ᶠ n in atTop, K.bulk sz κ (E n) n → ∀ x : Idx d (sz.L n) (sz.W n),
        ∫ ω, ‖Gres (ouMatC (K.M sz) n (t n) ω)
            ((E n : ℂ) + ((ouEtaLL sz τU n : ℝ) : ℂ) * Complex.I) true x x‖ ^ (2 * p)
          ∂(ouP (K.M sz).toUNModel n) ≤ Nsz sz n ^ δ

/-- **`UNOUEq747k`**: `UNOUEq747` for the kind `K` with the profile `P`: the expectation half of
`QDiff` for `𝐇_t` at the QUE scale `z_n = E_n + i η_Q` (`η_Q = ouEtaQ sz 𝔡 n`, fixed by the window of
`UNOUQUEk`), error `qdBoundExp sz n τ η_Q` (supervisor 0956 O3), profile `P` at `ζ(t_n)`; bulk inside `∀ᶠ n`. -/
def UNOUEq747k {d : ℕ} (K : UNKind d) (P : UNOUProfile K) (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ,
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ : ℝ, 0 < τ →
      ∀ᶠ n in atTop, K.bulk sz κ (E n) n → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMatC (K.M sz) n (t n) ω)
              ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y‖ ^ 2 : ℝ) : ℂ)) a b
            ∂(ouP (K.M sz).toUNModel n)) -
          P.pm sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) ∧
        ‖(∫ ω, avg2 sz n (fun x y =>
              Gres (ouMatC (K.M sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true x y *
              Gres (ouMatC (K.M sz) n (t n) ω)
                ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) true y x) a b
            ∂(ouP (K.M sz).toUNModel n)) -
          P.pp sz n (ouZeta (t n)) ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) a b‖ ≤
            qdBoundExp sz n τ (ouEtaQ sz 𝔡 n)

/-- **Row `UNG1Rowk`** (UN-51, `RandomLayerB` `g1Rowk`, class P): the two layer pins of every kind
from the kind's inputs `ML`, `Loc`, `Que` (band: `∀ d, UNMLOut d`, `UNLocAvgBand`, `UNQueBand`;
BA: `∀ d, UNMLOutBA d`, `UNLocAvgBA`, `UNQueBA`), at `τ_U ≤ ouTauMax 𝔠 𝔡`. -/
def UNG1Rowk (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) (ML Loc Que : Prop) : Prop :=
  ML → Loc → Que →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ τU : ℝ, 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 →
        UNOULLk (K d) sz τU ∧ UNOUEq747k (K d) (P d) sz 𝔡 τU

/-- **Row `UNG2bRowk`** (UN-52, `QUEFlow` `g2bRowk`, class P): `UNOUQUEk` from `UNOUEq747k` and the
profile's row differences, for every kind and profile; no `τ_U ≤ ouTauMax` (supervisor 0956 O2). -/
def UNG2bRowk (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) : Prop :=
  ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (K d) (P d) → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ τU : ℝ, 0 < τU → UNOUEq747k (K d) (P d) sz 𝔡 τU → UNOUQUEk (K d) sz 𝔡 τU

/-! ## 4. Target statements (each target's statement is the body of `T2282_<name>`) -/

/-! ### 4.1 generic (§3) -/

def T2282_ouDiagk_of_ouLLk : Prop :=
  ∀ {d : ℕ} {K : UNKind d} {sz : Sizes d} {τU : ℝ}, UNOULLk K sz τU → UNOUDiagk K sz τU

def T2282_ouRowk_of_pins : Prop :=
  ∀ (K : ∀ d, UNKind d) (P : ∀ d, UNOUProfile (K d)) {ML Loc Que : Prop},
    (∀ d : ℕ, 3 ≤ d → UNOUProfRowk (K d) (P d)) →
      UNG1Rowk K P ML Loc Que → UNG2bRowk K P → UNOURowk K ML Loc Que

/-! ### 4.2 band bridges (§4): T2276's pins are the band instance -/

def T2282_unOUProfRowk_band : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → UNOUProfRowk (UNKind.band d) (UNOUProfile.band d)

def T2282_UNOULLk_band : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (τU : ℝ), UNOULLk (UNKind.band d) sz τU ↔ UNOULL sz τU

def T2282_UNOUEq747k_band : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (𝔡 τU : ℝ),
    UNOUEq747k (UNKind.band d) (UNOUProfile.band d) sz 𝔡 τU ↔ UNOUEq747 sz 𝔡 τU

def T2282_UNG1Rowk_band : Prop :=
  UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand ↔ UNG1Row

def T2282_unG2bRow_of_k : Prop :=
  UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) → UNG2bRow

def T2282_ouRow_of_pinsk_band : Prop :=
  UNG1Rowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d)
      (∀ d : ℕ, UNMLOut d) UNLocAvgBand UNQueBand →
    UNG2bRowk (fun d => UNKind.band d) (fun d => UNOUProfile.band d) → UNOURow

/-! ## 5. Prop-valued examples (shapes only; no proof obligation) -/

example : Prop := T2282_ouRowk_of_pins
example : Prop := UNOULLk (UNKind.band 3) RBM.Gauss.SizesInst.sz0 (1 / 1000)
example : Prop :=
  UNOUEq747k (UNKind.band 3) (UNOUProfile.band 3) RBM.Gauss.SizesInst.sz0 (1 / 10) (1 / 1000)
example : Prop := UNOUProfRowk (UNKind.band 3) (UNOUProfile.band 3)
example : Prop := UNOUDiagk (UNKind.band 3) RBM.Gauss.SizesInst.sz0 (1 / 1000)
-- The BA consumer (BA-C3; not a target here): once BA-C3 supplies `P` and its row differences,
-- `UNOURowBA` (`BA/UNPins.lean:123`) is `ouRowk_of_pins` at `UNKind.ba`.
example : Prop :=
  ∀ P : ∀ d, UNOUProfile (UNKind.ba d), (∀ d : ℕ, 3 ≤ d → UNOUProfRowk (UNKind.ba d) (P d)) →
    UNG1Rowk (fun d => UNKind.ba d) P (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA →
      UNG2bRowk (fun d => UNKind.ba d) P → UNOURowBA

end RBM.Univ.T2282Check
