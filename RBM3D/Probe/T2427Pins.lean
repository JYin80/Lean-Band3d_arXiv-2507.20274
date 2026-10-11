/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins
import RBM3D.Chain.LWGen
import RBM3D.Chain.Carrier
import RBM3D.BA.FlowPins
import RBM3D.Defs.Sizes
import RBM3D.Gauss.FineModel
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.LWExpTerm
import RBM3D.BA.GreenSchur
import RBM3D.BA.GreenLDE
import RBM3D.BA.Ward
import RBM3D.BA.MFixedPoint
import RBM3D.BA.CombesThomas

/-!
# T2427 probe (BA stage TL, row TL1a, design gate): the statements of targets 1-2

Never merged; statements only (Prop-valued definitions; proof terms occur only in the `example`s), compiled against `main`;
the `example`s are the nonemptiness instances.  Route (R-a): `baLanlw_holds` (`Graph/BAExpand.lean:744`)
with `f = Φ_p = T^{p-1} conj(T)^p`, transported to `μ = seqP (sz.withLam 0)` as `BAExp14a_lanlw_diag`
(`Graph/BAExp14aB.lean:733`).  `lanlw` writes `Ǧ = -M(V + tm)G`, the mirror of `TP:72`, so the identity is in the
mirror form, in the `twTr` convention (`twTr c₁ c₂ = T̃_{(c₂,c₁)}`, `TwistPins.lean:57-60`): `P = P_{c₂c₁}`.

Plan of the two files (each pin `P` below is proved as `P_holds : ∀ d, P d`; helpers are private or stem-prefixed `TwistAvgA_*`, `TwistAvgA2_*`, rule (E)):
* `RBM3D/BA/TwistAvgA.lean` (Steps 1-3): `BATwistAvgRecAt`, `BATwistAvgRec` (head), `twAvgGPM`, `twAvgGPG`, `twAvgS1`, `twAvgS2`, `twAvgX`, `twAvgXmax`,
  `twAvgMomentAt`/`twAvgMoment` (target 2 (i)), `twAvgReg` (target 2 (iv)).
* `RBM3D/BA/TwistAvgA2.lean` (Step 4, first display of Step 5): `twAvgSCS`, `twAvgSPrec` (target 2 (ii)), `twAvgT6` (target 2 (iii)), Hölder, `baTwistAvgRec_holds`
  (target 1), the instances.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Definitions: `(GPM)`, `(GPG)`, `𝒮₁`, `𝒮₂`, `X_{c₁c₂}`, `X` -/

section TwistAvg
variable {d : ℕ} {sz : Sizes d}

/-- `(G P M)_{βα} = W^{-d} Σ_{w ∈ [c₁]} G_{β, Π_{c₂} w} M_{wα}`, `P = P_{c₂c₁}` (so `Tr(Ǧ P) = twTr c₁ c₂`). -/
def twAvgGPM (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (β α : Idx d (sz.L n) (sz.W n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c₁, C.G n t ω β (twShift n c₂ w) * C.M n w α

/-- `(G P G)_{αβ} = W^{-d} Σ_{w ∈ [c₁]} G_{α, Π_{c₂} w} G_{wβ}`; `∂_{h_{βα}} twTr c₁ c₂ = -(G P G)_{αβ}`. -/
def twAvgGPG (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (α β : Idx d (sz.L n) (sz.W n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c₁, C.G n t ω α (twShift n c₂ w) * C.G n t ω w β

/-- `𝒮₁ = Σ_{α,β} S_{αβ} (GPM)_{βα} (GPG)_{αβ}` (TP:78, mirror form), `S_{αβ} = W^{-d} S^{(B)}_{[α][β]}` (no factor `t`; `S^{(B)} = I` at BA). -/
def twAvgS1 (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ∑ α, ∑ β, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
    (twAvgGPM C n t ω c₁ c₂ β α * twAvgGPG C n t ω c₁ c₂ α β)

/-- `𝒮₂ = Σ_{α,β} S_{αβ} (GPM)_{βα} conj((GPG)_{βα})` (TP:78, mirror form). -/
def twAvgS2 (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ∑ α, ∑ β, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) β).1 *
    (twAvgGPM C n t ω c₁ c₂ β α * (starRingEnd ℂ) (twAvgGPG C n t ω c₁ c₂ β α))

/-- `X_{c₁c₂} = (𝔼_μ ‖twTr … c₁ c₂‖^{2p})^{1/(2p)}` (TP:86). -/
def twAvgX (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (t : ℝ) (p : ℕ) (c₁ c₂ : Zd d (sz.L n)) : ℝ :=
  (∫ ω, ‖twTr C n t ω c₁ c₂‖ ^ (2 * p) ∂μ) ^ ((1 : ℝ) / (2 * (p : ℝ)))

/-- `X = max_{c₁,c₂} X_{c₁c₂}` (a maximum over the `L^{2d}` ordered pairs). -/
def twAvgXmax (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (t : ℝ) (p : ℕ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩
    fun q : Zd d (sz.L n) × Zd d (sz.L n) => twAvgX C μ n t p q.1 q.2

/-! ## 2. Target 2 (i): the moment identity of Steps 1-3 (TP:70-78, 86-87), mirror form, at the BA carrier and the BA law -/

/-- `𝔼|T|^{2p} = t Σ_c M_{c₁c} 𝔼[X_c (M_{cc₂} + twTr c c₂) Φ] + t(p-1) 𝔼[𝒮₁ T^{p-2} T̄^p] + t p 𝔼[𝒮₂ |T|^{2p-2}]`, `T = twTr c₁ c₂`,
`Φ = T^{p-1} T̄^p`, `X_c = 𝓛^{(1)}_{+,c} - m = Tr(Ǧ E_c)`, `M_{ab} = twMB` (`M^{(B)}`).  An exact identity at one size `n` and one time `t`. -/
def twAvgMomentAt (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (p : ℕ) (c₁ c₂ : Zd d (sz.L n)) : Prop :=
  let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
  ((∫ ω, ‖twTr C n t ω c₁ c₂‖ ^ (2 * p) ∂μ : ℝ) : ℂ) =
    (t : ℂ) * ∑ c, twMB C n c₁ c * ∫ ω, (C.L n t (fun _ : Fin 1 => true) (fun _ => c) ω - C.m n) *
        (twMB C n c c₂ + twTr C n t ω c c₂) * twTr C n t ω c₁ c₂ ^ (p - 1) * (starRingEnd ℂ) (twTr C n t ω c₁ c₂) ^ p ∂μ +
    (t : ℂ) * ((p : ℂ) - 1) * ∫ ω, twAvgS1 C n t ω c₁ c₂ * twTr C n t ω c₁ c₂ ^ (p - 2) * (starRingEnd ℂ) (twTr C n t ω c₁ c₂) ^ p ∂μ +
    (t : ℂ) * (p : ℂ) * ∫ ω, twAvgS2 C n t ω c₁ c₂ * ((‖twTr C n t ω c₁ c₂‖ ^ (2 * p - 2) : ℝ) : ℂ) ∂μ

/-- **Target 2 (i)**: `twAvgMomentAt` for every flow datum, `n`, `0 ≤ t ≤ T₀`, `p ≥ 1`, pair `(c₁, c₂)` (no `3 ≤ d`: `lanlw` is for every `d`). -/
def twAvgMoment (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n →
    ∀ p : ℕ, 1 ≤ p → ∀ c₁ c₂ : Zd d (sz.L n), twAvgMomentAt sz z n t p c₁ c₂

/-! ## 3. Target 2 (ii): Step 4 (TP:80-85): Cauchy-Schwarz in `(o', o)`, then `≺ B²` -/

/-- **Target 2 (ii), deterministic half** (the loop pairs of TP:83 in the mirror form): `|𝒮₁| ≤ Σ_c |M_{c₁c}| (|𝓛⁴_{(++--),(c,c₂,c,c₁)}| |𝓛²_{(+-),(c₂,c)}|)^{1/2}`,
`|𝒮₂| ≤ Σ_c |M_{c₁c}| (|𝓛⁴_{(-+-+),(c,c₂,c,c₂)}| |𝓛²_{(+-),(c,c₁)}|)^{1/2}`; pathwise. -/
def twAvgSCS (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n →
    ∀ (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)),
      ‖twAvgS1 (baFMz sz z) n t ω c₁ c₂‖ ≤ ∑ c, ‖twMB (baFMz sz z) n c₁ c‖ * Real.sqrt
        (‖(baFMz sz z).L n t ![true, true, false, false] ![c, c₂, c, c₁] ω‖ * ‖(baFMz sz z).L n t ![true, false] ![c₂, c] ω‖) ∧
      ‖twAvgS2 (baFMz sz z) n t ω c₁ c₂‖ ≤ ∑ c, ‖twMB (baFMz sz z) n c₁ c‖ * Real.sqrt
        (‖(baFMz sz z).L n t ![false, true, false, true] ![c, c₂, c, c₂] ω‖ * ‖(baFMz sz z).L n t ![true, false] ![c, c₁] ω‖)

/-- **Target 2 (ii)**: `‖𝒮₁‖ + ‖𝒮₂‖ ≺ B²` uniformly in `(c₁, c₂)`, from `STLmaxgL` (`k = 2, 4`) and `BAMB_row_l1` (the constant `C_M` is absorbed by `≺`). -/
def twAvgSPrec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLmaxgL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n q ω => ‖twAvgS1 (baFMz sz z) n (t n) ω q.1 q.2‖ + ‖twAvgS2 (baFMz sz z) n (t n) ω q.1 q.2‖)
        (fun n _ _ => sz.Bctl n (t n) ^ 2)

/-! ## 4. Target 2 (iii): Lemma T.6 at the law `μ` (TP:60) -/

/-- **Target 2 (iii)**: `𝔼[ξ Y] ≤ N^ε R 𝔼Y + N^{-D} (𝔼Y²)^{1/2}` for `ξ ≥ 0` with `ξ ≺ R` (`R ≥ 0` deterministic), `ξ ≤ N^{Kenv}` pointwise, `Y ≥ 0`
measurable with `𝔼Y² < ∞`; at an arbitrary probability law `μ` on the common sample space (the `≺` is `PrecL`, `StochDomAt` at the scale `N = sz.size n`). -/
def twAvgT6 : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] {V : ℕ → Type} (ξ : ∀ n, V n → sz.SeqΩ → ℝ) (R : ∀ n, V n → ℝ) (Kenv : ℝ),
    sz.SizeTendsto → (∀ n v ω, 0 ≤ ξ n v ω) → (∀ n v, 0 ≤ R n v) → (∀ᶠ n in atTop, ∀ v ω, ξ n v ω ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv) →
    PrecL sz μ ξ (fun n v _ => R n v) → ∀ ε D : ℝ, 0 < ε → 0 < D → ∀ᶠ n in atTop, ∀ (v : V n) (Y : sz.SeqΩ → ℝ), Measurable Y → (∀ ω, 0 ≤ Y ω) →
      Integrable (fun ω => Y ω ^ 2) μ →
      ∫ ω, ξ n v ω * Y ω ∂μ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * R n v * ∫ ω, Y ω ∂μ + ((sz.size n : ℕ) : ℝ) ^ (-D) * (∫ ω, Y ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2)

/-! ## 5. Target 2 (iv): continuity (measurability, integrability) and deterministic envelopes -/

/-- **Target 2 (iv)**: for `0 ≤ t ≤ T₀`: `twTr`, `𝒮₁`, `𝒮₂`, `𝓛^{(1)}_c - m` are continuous in `ω` (so measurable), `‖twTr‖^p` is integrable at `μ`, and the four are bounded by
`η_t⁻¹ + 1`, resp. `N (η_t⁻¹ + 1)³` (`‖G_{xy}‖ ≤ η_t⁻¹`, `‖M_{xy}‖ ≤ 1`, `Σ_{α,β} S_{αβ} = N`); eventually in `n`, uniformly in `t`, `η_t⁻¹ + 1 ≤ N`
(`η_t ≥ η_{T₀} = √T₀ Im z_n ≥ √(κ/(κ+1)) N^{-1+ε}`), so that all four are `≤ N^4` (`Kenv = 4` of `twAvgT6`). -/
def twAvgReg (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
    (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ c₁ c₂ : Zd d (sz.L n),
      Continuous (fun ω => twTr (baFMz sz z) n t ω c₁ c₂) ∧ Continuous (fun ω => twAvgS1 (baFMz sz z) n t ω c₁ c₂) ∧
      Continuous (fun ω => twAvgS2 (baFMz sz z) n t ω c₁ c₂) ∧
      Continuous (fun ω => (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c₁) ω - (baFMz sz z).m n) ∧
      ∀ p : ℕ, Integrable (fun ω => ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ^ p) (Sizes.seqP (sz.withLam 0))) ∧
    (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)),
      ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 ∧
      ‖(baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c₁) ω - (baFMz sz z).m n‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 ∧
      ‖twAvgS1 (baFMz sz z) n t ω c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (((baFMz sz z).eta n t)⁻¹ + 1) ^ 3 ∧
      ‖twAvgS2 (baFMz sz z) n t ω c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (((baFMz sz z).eta n t)⁻¹ + 1) ^ 3) ∧
    ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n → ((baFMz sz z).eta n t)⁻¹ + 1 ≤ ((sz.size n : ℕ) : ℝ)

/-! ## 6. Target 1: the pin `BATwistAvgRec` (the 2p-moment recursion, TP:89 first display) and the interface to TL1b -/

/-- The recursion at one carrier, law and time sequence, with the constant `K` (`= C_M` of `BAMB_row_l1`, `+ 1`) kept: for every `p ≥ 1`, `ε' > 0`, `D > 0`,
eventually in `n`, for every ordered pair `(c₁, c₂)`, `B = Bctl n (t n)`:
`X_{c₁c₂}^{2p} ≤ K W^{ε'} B (X_{c₁c₂}^{2p-1} + X X_{c₁c₂}^{2p-1}) + 2p K W^{ε'} B² X_{c₁c₂}^{2p-2} + N^{-D}`. -/
def BATwistAvgRecAt (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (K : ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ ε' D : ℝ, 0 < ε' → 0 < D → ∀ᶠ n in atTop, ∀ c₁ c₂ : Zd d (sz.L n),
    twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p) ≤
      K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n)) * (twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 1) + twAvgXmax C μ n (t n) p * twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 1)) +
      2 * (p : ℝ) * K * (((sz.W n : ℕ) : ℝ) ^ ε' * sz.Bctl n (t n) ^ 2) * twAvgX C μ n (t n) p c₁ c₂ ^ (2 * p - 2) + ((sz.size n : ℕ) : ℝ) ^ (-D)

/-- **Target 1: the pin.**  Frame and premises of `BATwistAvgProd` (`TwistPins.lean:154`); the constant `K` is fixed before `𝔠, sz, z` (the O2 form of `twK_bound`). -/
def BATwistAvgRec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ K : ℝ, 0 < K ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → BATwistAvgRecAt (baFMz sz z) μ t K

/-- The interface to TL1b (statement only): the bootstrap with S1, Markov at `μ`, the union over the pairs. -/
def T2427_TL1b : Prop := ∀ d, BATwistAvgRec d → BATwistAvgProd d

/-! ## 7. Instances (target 3): `d = 3`, `sz0` (`L = 4`, `W = 32` at `n = 0`), `zSeq`, `flow_sz0`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`, `t ≡ 1/2 ≤ T₀`.
Other gates' pins (`LWAvgLawgL`, `STLmaxgL`) stay hypotheses; every deterministic hypothesis is discharged. -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.MFixedPointInst
local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- Target 1 at the datum: `BATwistAvgRec 3` gives a constant `K > 0` and the recursion at `(sz0, zSeq)`, `t ≡ 1/2`. -/
example (h : BATwistAvgRec 3) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    ∃ K : ℝ, 0 < K ∧ BATwistAvgRecAt (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) K := by
  obtain ⟨K, hK, H⟩ := h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨K, hK, H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM⟩

/-- Target 1, non-vacuity of the conclusion: at `p = 1`, `ε' = 1/10`, `D = 1`, for every `n` of an eventual set there is a pair `c₂ ≠ c₁` of blocks
at which the recursion holds (`atTop` on `ℕ` is `NeBot`). -/
example (h : BATwistAvgRec 3) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∃ c₁ c₂ : Zd 3 (sz0.L n), c₂ ≠ c₁ ∧
      twAvgX (baFMz sz0 zSeq) μ0 n (1 / 2) 1 c₁ c₂ ^ (2 * 1) ≤
        K * (((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * sz0.Bctl n (1 / 2)) * (twAvgX (baFMz sz0 zSeq) μ0 n (1 / 2) 1 c₁ c₂ ^ (2 * 1 - 1) +
          twAvgXmax (baFMz sz0 zSeq) μ0 n (1 / 2) 1 * twAvgX (baFMz sz0 zSeq) μ0 n (1 / 2) 1 c₁ c₂ ^ (2 * 1 - 1)) +
        2 * ((1 : ℕ) : ℝ) * K * (((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * sz0.Bctl n (1 / 2) ^ 2) * twAvgX (baFMz sz0 zSeq) μ0 n (1 / 2) 1 c₁ c₂ ^ (2 * 1 - 2) +
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨K, hK, H⟩ := h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  filter_upwards [H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hA hM 1 le_rfl (1 / 10) 1
    (by norm_num) (by norm_num)] with n hn
  have : Fact (1 < sz0.L n) := ⟨by have := sz0.three_le_L n; omega⟩
  exact ⟨0, ![1, 0, 0], fun hh => by simpa using congrFun hh 0, hn 0 ![1, 0, 0]⟩

/-- Target 2 (i) at `n = 0` (`L = 4`, `W = 32`), `t = 1/2`, `p = 1` and `p = 2`, `c₁ = 0`, `c₂ = (1,0,0) ≠ c₁`. -/
example (h : twAvgMoment 3) : twAvgMomentAt sz0 zSeq 0 (1 / 2) 1 0 ![1, 0, 0] :=
  h (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0 0 (1 / 2) (by norm_num) (half_lt_t0 0).le 1 le_rfl 0 ![1, 0, 0]
example (h : twAvgMoment 3) : twAvgMomentAt sz0 zSeq 0 (1 / 2) 2 0 ![1, 0, 0] :=
  h (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0 0 (1 / 2) (by norm_num) (half_lt_t0 0).le 2 (by norm_num) 0 ![1, 0, 0]
example : (![1, 0, 0] : Zd 3 (sz0.L 0)) ≠ 0 := by
  have : Fact (1 < sz0.L 0) := ⟨by decide⟩
  exact fun hh => by simpa using congrFun hh 0

/-- Target 2 (ii), deterministic half, at `n = 0`, `t = 1/2`, any sample `ω`, `c₁ = 0`, `c₂ = (1,0,0)`. -/
example (h : twAvgSCS 3) (ω : (sz0).SeqΩ) :=
  h (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0 0 (1 / 2) (by norm_num) (half_lt_t0 0).le ω 0 ![1, 0, 0]

/-- Target 2 (ii), `≺` form, at the datum (`STLmaxgL` is another gate's pin). -/
example (h : twAvgSPrec 3) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    PrecL sz0 μ0 (U := fun n => Zd 3 (sz0.L n) × Zd 3 (sz0.L n))
      (fun n q ω => ‖twAvgS1 (baFMz sz0 zSeq) n (1 / 2) ω q.1 q.2‖ + ‖twAvgS2 (baFMz sz0 zSeq) n (1 / 2) ω q.1 q.2‖)
      (fun n _ _ => sz0.Bctl n (1 / 2) ^ 2) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hM

/-- Target 2 (iv) at the datum: the pointwise bound `‖twTr‖ ≤ η⁻¹ + 1` and the eventual envelope `η⁻¹ + 1 ≤ N` at `t = 1/2` give `‖twTr‖ ≤ N`, for all blocks `c₁, c₂`. -/
example (h : twAvgReg 3) : ∀ᶠ n in atTop, ∀ (ω : sz0.SeqΩ) (c₁ c₂ : Zd 3 (sz0.L n)),
    ‖twTr (baFMz sz0 zSeq) n (1 / 2) ω c₁ c₂‖ ≤ ((sz0.size n : ℕ) : ℝ) := by
  obtain ⟨-, hb, he⟩ := h (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0
  filter_upwards [he] with n hn ω c₁ c₂
  exact (hb n (1 / 2) (by norm_num) (half_lt_t0 n).le ω c₁ c₂).1.trans (hn (1 / 2) (by norm_num) (half_lt_t0 n).le)

/-- Target 2 (iii) at the datum: `ξ_c = ‖𝓛^{(1)}_c - m‖ ≺ B = Bctl n (1/2)` (`LWAvgLawgL`, a pin), `ξ ≤ N` (target 2 (iv)), `R = Bctl > 0`, `Y ≡ 1`, `ε = D = 1/2`
(the law is `BAExp14a_μ sz0 = seqP (sz0.withLam 0)`, `Graph/BAExp14aB.lean:649`, which carries the probability-measure instance on `sz0.SeqΩ`). -/
example (hT6 : twAvgT6) (hreg : twAvgReg 3) (hA : LWAvgLawgL (baFMz sz0 zSeq) (BAExp14a_μ sz0) (fun _ => 1 / 2)) :
    ∀ᶠ n in atTop, ∀ c : Zd 3 (sz0.L n),
      ∫ ω, ‖(baFMz sz0 zSeq).L n (1 / 2) (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz0 zSeq).m n‖ * 1 ∂(BAExp14a_μ sz0) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * sz0.Bctl n (1 / 2) * ∫ ω, (1 : ℝ) ∂(BAExp14a_μ sz0) +
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * (∫ ω, (1 : ℝ) ^ 2 ∂(BAExp14a_μ sz0)) ^ ((1 : ℝ) / 2) := by
  obtain ⟨-, hb, he⟩ := hreg (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq (by norm_num) flow_sz0
  have henv : ∀ᶠ n in atTop, ∀ (c : Zd 3 (sz0.L n)) (ω : sz0.SeqΩ),
      ‖(baFMz sz0 zSeq).L n (1 / 2) (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz0 zSeq).m n‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) := by
    filter_upwards [he] with n hn c ω
    rw [Real.rpow_one]
    exact (hb n (1 / 2) (by norm_num) (half_lt_t0 n).le ω c c).2.1.trans (hn (1 / 2) (by norm_num) (half_lt_t0 n).le)
  filter_upwards [hT6 sz0 (BAExp14a_μ sz0) (V := fun n => Zd 3 (sz0.L n))
    (fun n c ω => ‖(baFMz sz0 zSeq).L n (1 / 2) (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz0 zSeq).m n‖) (fun n _ => sz0.Bctl n (1 / 2)) 1
    sz0_tendsto (fun _ _ _ => norm_nonneg _) (fun n _ => (STBctl_pos sz0 n (by norm_num)).le) henv hA (1 / 2) (1 / 2) (by norm_num) (by norm_num)] with n hn c
  exact hn c (fun _ => 1) measurable_const (fun _ => zero_le_one) (integrable_const _)

end Inst

end TwistAvg

end RBM.BA

end

/-! ## 8. `#check` of every probe name -/

set_option format.width 250
open RBM.BA
#check @twAvgGPM
#check @twAvgGPG
#check @twAvgS1
#check @twAvgS2
#check @twAvgX
#check @twAvgXmax
#check @twAvgMomentAt
#check @twAvgMoment
#check @twAvgSCS
#check @twAvgSPrec
#check @twAvgT6
#check @twAvgReg
#check @BATwistAvgRecAt
#check @BATwistAvgRec
#check @T2427_TL1b
