/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.LWPinsBA
import RBM3D.BA.GreenSchur
import RBM3D.BA.EKPins
import RBM3D.Induction.Step1Setup
import RBM3D.Kernel.Evolution
import RBM3D.Induction.DecayLoopA
import RBM3D.Induction.MainIndChain

/-!
# BA stage TL, row TL0 (T2421): pins of the twisted loops and their model-free lemmas

The vocabulary of the twisted loops (`twBlk`, `twShift`, `twTr`, `twLoopX`, `twL2'`, `twK`),
the two owed pins `BATwistAvgLaw` (TL1, Lemma T.7) and `BATwistLoopLaw` (TL2, Theorem T.12),
the statements the later TL rows prove (`BATwistAvgProd`, `BATwistLoopStep`, `BATwistLoopBase`,
`BAMainIndTL`, `BAMLOutTL`, `BAChainTL`, `BATwKer*`, `BATwistZeroMode`, `BATwistSrc1`-`5`),
and the model-free lemmas `twTr_eq`, `twMB_ba`, `twK_ba`, `twFold_holds`, `twWard_holds`,
`twCirc_holds`, `twK_bound_holds`.  Sections 1-3 are copied from
`t/T2413:RBM3D/Probe/T2413Pins.lean` at `76c586e` (design `docs/reports/T2413-design.md`); the
one statement that differs is `twK_bound`: `∀ᶠ n in atTop` in place of `∀ n` (Amend 1,
paper-delta candidate T2421a).
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

/-! ## 1. Verbatim from `t/T2398:RBM3D/Probe/T2398Pins.lean` (`6429bb5`) -/

section Twist
variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)
/-- The fine vertices of the block `a`. -/
def twBlk (n : ℕ) (a : Zd d (sz.L n)) : Finset (Idx d (sz.L n) (sz.W n)) :=
  Finset.univ.filter fun x => (split d (sz.L n) (sz.W n) x).1 = a
/-- The offset-preserving shift into the block `c`: `x = (a, o) ↦ (c, o)`.  `M_{xy} = 1[offset x = offset y] M^{(B)}_{[x][y]}`
(`BAMfine_eq`) ties vertices exactly by this map. -/
def twShift (n : ℕ) (c : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) : Idx d (sz.L n) (sz.W n) :=
  (splitEquiv d (sz.L n) (sz.W n)).symm (c, (split d (sz.L n) (sz.W n) x).2)
/-- The offset-twisted one-loop `W^{-d} Σ_{w ∈ [c₁]} Ǧ_{w, Π_{c₂} w} = W^{-d} Σ_o Ǧ_{(c₁,o),(c₂,o)}`, i.e. `Tr(Ǧ P_{c₂c₁})` in the convention below (`twTr_eq`).  It
occurs in the family `T3B` of `GGGamma` (`Ǧ_{αw} M_{wα}`); for `c₂ = c₁` it is `tr(Ǧ E_{c₁})`. -/
def twTr (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c₁, C.GM n t ω w (twShift n c₂ w)
/-! ### Index convention of the twisted objects (supervisor 0652 C3; `docs/tickets/T2398-TL-proofs.md` A.2): the proofs', used below

`P_{c₁c₂} = W^{-d} Σ_o |(c₁,o)⟩⟨(c₂,o)|`, so `Tr(X P_{c₁c₂}) = W^{-d} Σ_o X_{(c₂,o),(c₁,o)}` (`twTrP`); `G(+) = G`, `G(−) = G^*` (`twChg`); `L̃_{σ,(a;c₁,c₂)} = Tr(G(σ₁) E_a G(σ₂) P_{c₁c₂}) = W^{-2d} Σ_o Σ_{x∈[a]} G(σ₁)_{(c₂,o),x} G(σ₂)_{x,(c₁,o)}` (`twLoopX`, `twL2'`).  The probe's `twL2 … a c₁ c₂` is `L̃_{(−,+),(a;c₁,c₂)}` with the leg at `c₁` circled (`twL2_eq`); `twTr … c₁ c₂ = W^{-d} Σ_o Ǧ_{(c₁,o),(c₂,o)}` is `T̃_{+,(c₂,c₁)} = Tr(G̊ P_{c₂c₁})` (`twTr_eq`), and `T̃_{−,(c₁,c₂)} = conj T̃_{+,(c₂,c₁)}`: TL1 for all ordered pairs and one charge is the whole law.  `twK` is `K̃` of the proofs (B.1); `twCirc` is their A.2. -/
/-- `X(σ)` entrywise: `X(+) = X`, `X(−) = X^*` (`(X^*)_{xy} = conj X_{yx}`). -/
def twChg {ι : Type*} (X : ι → ι → ℂ) (σ : Bool) (x y : ι) : ℂ := if σ then X x y else (starRingEnd ℂ) (X y x)
/-- `Tr(X P_{c₁c₂}) = W^{-d} Σ_o X_{(c₂,o),(c₁,o)}` (`w = (c₂,o) ∈ [c₂]`). -/
def twTrP (n : ℕ) (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c₂, X w (twShift n c₁ w)
/-- `Tr(X₁ E_a X₂ P_{c₁c₂}) = W^{-2d} Σ_o Σ_{x∈[a]} (X₁)_{(c₂,o),x} (X₂)_{x,(c₁,o)}` (`w = (c₁,o) ∈ [c₁]`). -/
def twLoopX (n : ℕ) (X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, X₂ x w * X₁ (twShift n c₂ w) x
theorem twTr_eq (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) : twTr C n t ω c₁ c₂ = twTrP n (C.GM n t ω) c₂ c₁ := rfl
/-- **`L̃`, the uncircled twisted 2-loop** `Tr(G(σ₁)E_aG(σ₂)P_{c₁c₂})` (convention above). -/
def twL2' (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  twLoopX n (twChg (C.G n t ω) (σ 0)) (twChg (C.G n t ω) (σ 1)) a c₁ c₂
/-- `M^{(B)}_{ab} = M_{(a,0),(b,0)}`, read off the carrier's fine `M` (`BAMfine_eq`: `M_{xy} = 1[offsets equal] M^{(B)}_{[x][y]}`; `twMB_ba`). -/
def twMB (n : ℕ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Matrix.of fun a b => C.M n ((splitEquiv d (sz.L n) (sz.W n)).symm (a, 0)) ((splitEquiv d (sz.L n) (sz.W n)).symm (b, 0))
/-- **`K̃`, the explicit twisted tree** (proofs T.1 (B.1); supervisor 0652 C2): `K̃_{σ,(a;c₁,c₂)} = W^{-d} Σ_{a'} Θ^{(σ₁σ₂)}_t(a,a') M^{(B)}(σ₁)_{c₂a'} M^{(B)}(σ₂)_{a'c₁}`, `Θ^{(σ₁σ₂)}_t = (1 − t M^{(σ₁σ₂)})⁻¹` (`PropThetaQ`) of the carrier's `M`, `M^{(σ₁σ₂)}_{ab} = M^{(B)}(σ₁)_{ba} M^{(B)}(σ₂)_{ab}`: the entrywise product (`|M^{(B)}_{ab}|²` for `(−,+)`, not `M∘M`). -/
def twK (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n), PropThetaQ (BAMss d (sz.L n) (twMB C n) (σ 0) (σ 1)) t a a' *
    BAMsigma d (sz.L n) (twMB C n) (σ 0) c₂ a' * BAMsigma d (sz.L n) (twMB C n) (σ 1) a' c₁
/-- At the BA carrier `twMB` is `M^{(B)}` (`BAMfine_eq`), hence `twK` is built from `BATheta` (`BA/MFixedPoint.lean:515`, `rfl`) and `BAMB`. -/
theorem twMB_ba (z : ℕ → ℂ) (n : ℕ) (hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) :
    twMB (baFMz sz z) n = BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) := by
  ext a b
  have ha : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (a, 0)) = (a, 0) := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
  have hb : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (b, 0)) = (b, 0) := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
  simp only [twMB, Matrix.of_apply, baFMz, baFM]
  rw [BAMfine_eq sz _ _ n hm]
  change (if (split d (sz.L n) (sz.W n) _).2 = (split d (sz.L n) (sz.W n) _).2 then _ else _) = _
  rw [ha, hb]
  exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
/-- **TL1** (proofs Lemma T.7; supervisor 0652 Q1-Q3, C3: an owed text pin with the standing of `STLKgL`, a lemma of §8, a fixed-time consequence of (2.87), (2.89)): `|Tr(G̊ P_{c₂c₁})| ≺ W^{-d} B_{τ,0}` for every ordered pair `(c₁, c₂)` (`twTr`; one charge); `c₂ = c₁` is `LWAvgLawgL` (`twTr_diag`). -/
def BATwistAvgLaw (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ‖twTr C n (τ n) ω p.1 p.2‖)
    (fun n _ _ => sz.Bctl n (τ n))
/-- **TL2** (proofs Theorem T.12; supervisor 0652 Q1-Q3, C1, C2: an owed text pin, a fifth hypothesis and conclusion of Theorem 8.2; producer "TL stage (one step) + BA-V (induction)", base case `L̃_0 = K̃_0` from `G_0 = M`): `|L̃ − K̃| ≺ (W^{-d} B_{τ,0})^{3/2}` for the uncircled `twL2'`, all `σ ∈ {±}²`, all `(a, c₁, c₂)`, per `τ` like `STLKgL`; `3/2` is what `(B.1)` needs (the proofs give `2 − δ`); `twK` is explicit, no `∃ K̃`. -/
def BATwistLoopLaw (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖twL2' C n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK C n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
    (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ))
/-- `Tr(E_b X E_a X^*) = W^{-2d} Σ_{y∈[b]} Σ_{x∈[a]} |X_{yx}|²` (for `X = G(σ)`: the 2-loop `𝓛^{(2)}_{(σ,−σ),(a,b)}`). -/
def twSq (n : ℕ) (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (b a : Zd d (sz.L n)) : ℝ :=
  ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ∑ y ∈ twBlk n b, ∑ x ∈ twBlk n a, ‖X y x‖ ^ 2
/-- **`twFold`** (proofs T.2, (B.2)): `|Tr(X₁E_aX₂P_{c₁c₂})|² ≤ Tr(E_{c₂}X₁E_aX₁^*) Tr(E_aX₂E_{c₁}X₂^*)` for all matrices; with `X_i = G(σ_i)`: `|L̃_{σ,(a;c₁,c₂)}|² ≤ 𝓛^{(2)}_{(σ₁,−σ₁),(a,c₂)} 𝓛^{(2)}_{(σ₂,−σ₂),(a,c₁)}`. -/
def twFold (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (a c₁ c₂ : Zd d (sz.L n)),
    ‖twLoopX n X₁ X₂ a c₁ c₂‖ ^ 2 ≤ twSq n X₁ c₂ a * twSq n X₂ a c₁
/-- **`twWard`** (proofs T.3, `n = 2`; `Σ_a E_a = W^{-d}`): if `G − G^* = 2iη G G^* = 2iη G^* G` (the resolvent identities (2.53)), then for both charges `Σ_a Tr(G(σ)E_aG(−σ)P_{c₁c₂}) = (2iW^dη)⁻¹ (Tr(G P_{c₁c₂}) − Tr(G^* P_{c₁c₂}))`. -/
def twWard (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (G : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (η : ℝ), η ≠ 0 →
    G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G * G.conjTranspose) → G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G) →
    ∀ (σ : Bool) (c₁ c₂ : Zd d (sz.L n)), ∑ a, twLoopX n (twChg G σ) (twChg G (!σ)) a c₁ c₂ =
      (2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (η : ℂ))⁻¹ * (twTrP n (twChg G true) c₁ c₂ - twTrP n (twChg G false) c₁ c₂)
/-- **`twCirc`** (proofs A.2, the circled/uncircled relation): for `M_{wγ} = 1[offsets equal] M^{(B)}_{[w][γ]}` (`BAMfine_eq`; `M^{(B)}(σ₂)` for the charge of the slot), `Tr(X₁E_a(X₂ − M)P_{c₁c₂}) = Tr(X₁E_aX₂P_{c₁c₂}) − W^{-d} M^{(B)}_{ac₁} Tr(X₁P_{ac₂})`. -/
def twCirc (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (X₁ X₂ M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ),
    (∀ w γ, M w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
      MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0) →
    ∀ a c₁ c₂ : Zd d (sz.L n), twLoopX n X₁ (fun x y => X₂ x y - M x y) a c₁ c₂ =
      twLoopX n X₁ X₂ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB a c₁ * twTrP n X₁ a c₂
/-- **`twK_bound`** (proofs T.1 (i)-(ii); from `BAProp5`, `BAProp5mixed`, `BATheta_row_sum_pm`, `BAMB_row_l1`): at the BA flow `‖K̃‖ ≤ C W^{-d} B_{t,0}` (T.1 (i), `B_{t,|a−c₁|} ≤ B_{t,0}`, no decay in `|c₁ − c₂|`) and `Σ_a ‖K̃‖ ≤ C (W^d η_t)⁻¹` (T.1 (ii); `C = 1` in the proofs).  `C` is fixed before `sz`, `z` and depends on `(d, κ, ε, 𝔡)` only.
**Eventual in `n`** (T2421 Amend 1, paper-delta candidate T2421a; the probe `T2413Pins.lean:116-121` has `∀ n`): the window
`0 < g₀_n ≤ 𝔡⁻¹` that `BAProp5` and `BAMB_row_l1` need holds only eventually along `BAFlow` (`BAflow_lam0_window`, `Sizes.WO`). -/
def twK_bound (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
        (∀ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ C * sz.Bctl n (t n)) ∧
        ∑ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ C * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹

/-! ## 2. D1: the producer statements (carrier `baFMz sz z`, law `seqP (sz.withLam 0)` as `BAStep2`, `BA/FlowPins.lean:432`) -/

/-- Steps 1-4 on `[s,t]` as the premises of T.11, T.12' ((2.86)-(2.90), Claim 4.5, uniformly in `u ∈ [s,t]`): `STStep2ConclgL` is merged; the
other three are the carrier forms of `STLmaxU`, `STLKU` (`Induction/Step34Pins.lean:176, 184`) and `STDecayLoopU` (`DecayLoopB.lean:792`). -/
def twSteps (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STStep2ConclgL C μ s t Cd ∧
  (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))) ∧
  (∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ τ' D' : ℝ, 0 < τ' → 0 < D' → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')))

/-- The frame of T.11 and T.12': one BA main-induction step.  Constants first as `STStep2G` (`Chain/Step2Gen.lean:393`): `κ, ε, 𝔡`, the Step-2
loss `Cd`, then `𝔠d ≤ 1/100` (`c_d'` of T.12, below the `𝔠_d` of Steps 2-4), `𝔠`, sizes, `z`; regime `R` as `STStep3R` (`Step34Pins.lean:250`). -/
def BATwFrame (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Q : ∀ sz : Sizes d, FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
      (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t → sz.STConStInd 𝔠d s t → twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd →
        Q sz (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- **TL1 producer** (T.7, row TL1; fixed time, no induction): inputs (I2) `LWAvgLawgL` and (I3) `STLmaxgL` (`n = 2, 4`) at the time sequence `t`. -/
def BATwistAvgProd (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t

/-- **T.12'** (row TL2c, one induction step): (e_s) = TL2 at `s` and Steps 1-4 on `[s,t]` give TL2 at every time sequence `τ ∈ [s,t]` (per `τ`). -/
def BATwistLoopStep (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  BATwistLoopLaw C μ s → ∀ τ : ℕ → ℝ, (∀ n, s n ≤ τ n) → (∀ n, τ n ≤ t n) → BATwistLoopLaw C μ τ

/-- **The base case** `L̃_0 = K̃_0` (`G_0 = M`): TL2 at the zero sequence from the owed pin `STG0M` (`Induction/MainIndBase.lean:53`). -/
def BATwistLoopBase (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    STG0M (baFMz sz z) → BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) (fun _ => 0)

/-- **TL-V, the step with the fifth hypothesis and conclusion** (`STMainIndG`, `BA/FlowPins.lean:408`, plus TL2): owner BA-V (V2a).  Not on the route; superseded by the family form `BAMainIndFamTL` (V2a; design T2503; supervisor 2026-10-14-0342 V-F1); do not read. -/
def BAMainIndTL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ BAflowT0 sz z n) →
      (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → R sz s t → let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
      (STLKgL C μ s ∧ STDecaygL C μ s ∧ STDecayStronggL C μ s ∧ STLocalMaxgL C μ s ∧ STExp2gL C μ s ∧ BATwistLoopLaw C μ s) →
      sz.STConStInd 𝔠d s t → STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧
        STDecayStronggL C μ t ∧ BATwistLoopLaw C μ t

/-- **TL-V output** (the BA twin of `STMLOutG`, `Induction/MainIndOut.lean:51`, with TL2): at every `0 ≤ t_n ≤ T0`. -/
def BAMLOutTL (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let C := baFMz sz z; let μ := Sizes.seqP (sz.withLam 0)
      STLKgL C μ t ∧ STLmaxgL C μ t ∧ STDecaygL C μ t ∧ STExp2gL C μ t ∧ STLocalEntrygL C μ t ∧ BATwistLoopLaw C μ t

/-- **TL-V (row TL-V)**: the chain of times (`stPosConclG_of_mainIndG`, `MainIndChain.lean:148`, and the mixing of `stMLOutG_of_mainIndG`) with the TL2 conjunct.
`G_0 = M` at the carrier (`STG0M`, owed by BA-V `GLoopAtT0`) is a premise, in the form of `Induction/MainIndBase.lean:157`.  Reads the single-flow step `BAMainIndTL`; the route's chain is the family twin (V3; design T2503). -/
def BAChainTL (d : ℕ) : Prop :=
  BAMainIndTL d STAny → STHorizonG d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z) →
    STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz → BATwistLoopBase d →
      (∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) → BAMLOutTL d

/-! ## 3. D2: the BA kernels.  T.10 is about `Ũ_{v,u} = BAuKer v u` (`BA/EKPins.lean:49`, `(1 - v M^{(σ₁σ₂)}) Θ_u^{(σ₁σ₂)}` of `BAMss`, `BATheta`), T.11 about the sources of (D.4) -/

/-- **T.10 (a)** (`‖Ũ∘A‖_∞ ≤ ((1-v)/(1-u)) ‖A‖_∞`; the one-index factor of `baEKSumNdecay_holds`, whose proof `EKPins_norm_uKer_le` is private). -/
def BATwKerA (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ σ₁ σ₂ : Bool, ∀ v u : ℝ, 0 ≤ v → v ≤ u → u < 1 → ∀ A : Zd d L → ℂ,
      ‖BAuKer d L g E m v u σ₁ σ₂ *ᵥ A‖ ≤ (1 - v) / (1 - u) * ‖A‖

/-- **T.10 (b)** (the external anchor `c₁`, regime `u ≤ 1 - g²/L²`, `(D.6)`; from `baEKXiBall_holds` and (a)): `Ũ∘A` loses `W^{2ε} (g²+1-v)/(g²+1-u)`. -/
def BATwKerFar (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D →
    ∀ v u : ℝ, 0 ≤ v → v ≤ u → u ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - u) / (1 - v) → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ σ₁ σ₂ : Bool, ∀ (c₁ : Zd d L) (A : Zd d L → ℂ),
        (∀ b, W ^ ε * ellT L g v ≤ (zdistD d L (b - c₁) : ℝ) → ‖A b‖ ≤ W ^ (-D)) →
        ‖BAuKer d L g E m v u σ₁ σ₂ *ᵥ A‖ ≤ (1 + C₁ * W ^ (2 * ε) * ((g ^ 2 + |1 - v|) / (g ^ 2 + |1 - u|))) * ‖A‖ + W ^ (-D + 1)

/-- **T.10 (d)** (zero mode: `1 - v ≤ A g²/L²`, `Q^{(1)} = projMat`; the one-index factor of `baEKSumDecayNonzero_holds`, private `EKNonzero_norm_projMat_mul_uKer_le`).
The kernel has the flow coupling `g₀ ≤ g` (`BAflowLam0`) while the cases of Steps 3-6 are at the model `g`: `g² ≤ ((κ+1)/κ) g₀²` (K12, `KBound_B_le`), so the constant is `A = (κ+1)/κ`.
T.10 (c) (`σ₁ = σ₂`, `‖Ũ‖ ≤ C₂`) is the merged `BAEKSameRow` (`EKPins.lean:261`, `baEKSameRow_holds`). -/
def BATwKerZero (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ σ₁ σ₂ : Bool, ∀ v u : ℝ, 0 ≤ v → (1 - v) * (L : ℝ) ^ 2 ≤ A * g ^ 2 → v ≤ u → u < 1 →
      (open scoped Matrix.Norms.Operator in ‖projMat d L * BAuKer d L g E m v u σ₁ σ₂‖) ≤ C

/-- **T.12''** (row TL2c, `D_u = 0`, deterministic): for `σ₁ ≠ σ₂`, `Σ_a K̃_{σ,(a;c₁,c₂)} = (2i W^d η_t)⁻¹ (M^{(B)}_{c₂c₁} - (M^{(B)*})_{c₂c₁})`, `η_t = (1-t) Im m`
(`Θ^{(-,+)}_t` has row sums `(1-t)⁻¹`, `M^* M = (M - M^*)/(2i Im m)`): the Ward identity of the twisted tree. -/
def BATwistZeroMode (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) →
    (∀ n, t n ≤ BAflowT0 sz z n) → ∀ (n : ℕ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → ∀ c₁ c₂ : Zd d (sz.L n), ∑ a, twK (baFMz sz z) n (t n) σ a c₁ c₂ =
      (2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (((baFMz sz z).eta n (t n) : ℝ) : ℂ))⁻¹ *
        (BAMsigma d (sz.L n) (twMB (baFMz sz z) n) true c₂ c₁ - BAMsigma d (sz.L n) (twMB (baFMz sz z) n) false c₂ c₁)

/-- `Tr(G(σ₁)E_{a₁}G(σ₂)E_{a₂}G(σ₃)P_{c₁c₂})`, the twisted 3-loop `L̃^{(3)}` of (D.3) (`twLoopX` with one more vertex). -/
def twL3 (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 3 → Bool) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 * ∑ x ∈ twBlk n a₁, ∑ y ∈ twBlk n a₂, ∑ w ∈ twBlk n c₁,
    twChg (C.G n v ω) (σ 0) (twShift n c₂ w) x * twChg (C.G n v ω) (σ 1) x y * twChg (C.G n v ω) (σ 2) y w

/-- The sources of (D.4), (D.3): `B̃₁(v)(a) = W^d Σ_b K̃_v(b) (𝓛-𝒦)^{(2)}_{v,σ,(a,b)}`, `B̃₂` the same with `Z = L̃ - K̃` for `K̃`,
`Ẽ^{G̊}_v(a) = W^d Σ_{a'} [Tr(G̊₁E_{a'}) L̃^{(3)}_{(σ₁,σ₁,σ₂),(a',a)} + Tr(G̊₂E_{a'}) L̃^{(3)}_{(σ₁,σ₂,σ₂),(a,a')}]`, `Tr(G̊(σ)E_a) = 𝓛^{(1)}_{σ,a} - m(σ)`. -/
def twB1 (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b, twK C n v σ b c₁ c₂ * (C.L n v σ ![a, b] ω - C.K n v σ ![a, b])
def twB2 (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ b, (twL2' C n v ω σ b c₁ c₂ - twK C n v σ b c₁ c₂) * (C.L n v σ ![a, b] ω - C.K n v σ ![a, b])
def twEG (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  let tr : Bool → Zd d (sz.L n) → ℂ := fun τ a' => C.L n v ![τ] ![a'] ω - (if τ then C.m n else (starRingEnd ℂ) (C.m n));
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a', (tr (σ 0) a' * twL3 C n v ω ![σ 0, σ 0, σ 1] a' a c₁ c₂ + tr (σ 1) a' * twL3 C n v ω ![σ 0, σ 1, σ 1] a a' c₁ c₂)

/-- `∂_{xy} L̃_v(b) = -(G₁E_bG₂PG₁)_{yx} - (G₂PG₁E_bG₂)_{yx}` (D.2) and `(Ẽ⊗Ẽ)_v(b,b') = Σ_{x,y} S_{xy} ∂_{xy}L̃_v(b) \overline{∂_{xy}L̃_v(b')}`,
`S_{xy} = W^{-d} S^{(B)}_{[x][y]}` (`S^{(B)} = I` at BA); `Q_v(b) = (Ẽ⊗Ẽ)_v(b,b)`. -/
def twDer (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (b c₁ c₂ : Zd d (sz.L n)) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  let G₁ := twChg (C.G n v ω) (σ 0); let G₂ := twChg (C.G n v ω) (σ 1);
  -((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * (∑ z ∈ twBlk n b, ∑ w ∈ twBlk n c₁, G₁ y z * G₂ z w * G₁ (twShift n c₂ w) x +
    ∑ w ∈ twBlk n c₁, ∑ z ∈ twBlk n b, G₂ y w * G₁ (twShift n c₂ w) z * G₂ z x)
def twEE (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (b b' c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ∑ x, ∑ y, (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * C.S n (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 *
    (twDer C n v ω σ b c₁ c₂ x y * (starRingEnd ℂ) (twDer C n v ω σ b' c₁ c₂ x y))

/-- `|F_v(σ,a,c₁,c₂)| ≺ Ξ η_v^{-1} (W^{-d}B_{v,0})^e` uniformly in `v ∈ [s,t]`, `σ`, `a`, `c₁`, `c₂` (T.11 (i)-(iv)); `twDec`: `|F| ≤ W^{-D}` for `|a - c₁| ≥ 3 W^ε ℓ_v` (T.11 (v)). -/
def twSrc (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (F : ∀ n, ℝ → sz.SeqΩ → (Fin 2 → Bool) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ)
    (Ξ : ℕ → sz.SeqΩ → ℝ) (e : ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => F n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) (fun n p ω => Ξ n ω * ((C.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ e))
def twDec (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (F : ∀ n, ℝ → sz.SeqΩ → (Fin 2 → Bool) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => F n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 *
      (if 3 * ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) (p.1 : ℝ) ≤ (zdistInf d (sz.L n) (p.2.2.1 - p.2.2.2.1) : ℝ) then 1 else 0))
    (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **T.11 (i)-(v)** (row TL2b), each in the frame `BATwFrame`: (i) `B̃₁ ≺ η⁻¹ (W^{-d}B)²`; (ii) `Ẽ^{G̊} ≺ η⁻¹ (W^{-d}B)²`; (iii) `Q ≺ η⁻¹ (W^{-d}B)^{4-1/(2p)-1/q}`
for fixed `p, q`, and `|(Ẽ⊗Ẽ)(b,b')|² ≤ Q(b)Q(b')`; (iv) `B̃₂ ≺ Ξ̃ η⁻¹ (W^{-d}B)^{γ+1/6}` under `‖Z_v‖ ≤ Ξ̃ (W^{-d}B)^γ`, `γ ∈ [1,2]`, `Ξ̃ ≥ 1`; (v) decay of `B̃₁, B̃₂, Ẽ^{G̊}, Z` and of `(Ẽ⊗Ẽ)(·,b')` (the second index by `|(Ẽ⊗Ẽ)(b,b')| = |(Ẽ⊗Ẽ)(b',b)|`). -/
def BATwistSrc1 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  twSrc C μ s t (fun n v ω σ a c₁ c₂ => ‖twB1 C n v ω σ a c₁ c₂‖) (fun _ _ => 1) 2
def BATwistSrc2 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  twSrc C μ s t (fun n v ω σ a c₁ c₂ => ‖twEG C n v ω σ a c₁ c₂‖) (fun _ _ => 1) 2
def BATwistSrc3 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun _ C μ s t =>
  (∀ p q : ℕ, 1 ≤ p → 1 ≤ q → twSrc C μ s t (fun n v ω σ b c₁ c₂ => ‖twEE C n v ω σ b b c₁ c₂‖) (fun _ _ => 1)
    (4 - 1 / (2 * (p : ℝ)) - 1 / (q : ℝ))) ∧
  ∀ n v ω σ b b' c₁ c₂, ‖twEE C n v ω σ b b' c₁ c₂‖ ≤ Real.sqrt (‖twEE C n v ω σ b b c₁ c₂‖ * ‖twEE C n v ω σ b' b' c₁ c₂‖)
def BATwistSrc4 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun sz C μ s t =>
  ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → ∀ Ξ : ℕ → sz.SeqΩ → ℝ, (∀ n ω, 1 ≤ Ξ n ω) →
    (∀ n ω (v : ℝ) σ a c₁ c₂, s n ≤ v → v ≤ t n → ‖twL2' C n v ω σ a c₁ c₂ - twK C n v σ a c₁ c₂‖ ≤ Ξ n ω * sz.Bctl n v ^ γ) →
    twSrc C μ s t (fun n v ω σ a c₁ c₂ => ‖twB2 C n v ω σ a c₁ c₂‖) Ξ (γ + 1 / 6)
def BATwistSrc5 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop := BATwFrame d R fun sz C μ s t =>
  twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twB1 C n v ω σ a c₁ c₂‖) ∧ twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twB2 C n v ω σ a c₁ c₂‖) ∧
  twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twEG C n v ω σ a c₁ c₂‖) ∧ twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twL2' C n v ω σ a c₁ c₂ - twK C n v σ a c₁ c₂‖) ∧
  ∀ b' : ∀ n, Zd d (sz.L n), twDec μ s t (fun n v ω σ a c₁ c₂ => ‖twEE C n v ω σ a (b' n) c₁ c₂‖)

/-- **D2**: at the BA carrier `twK` is built from `BATheta`, `BAMss`, as `BAKsolve` (`BA/KSolve.lean:58`) and `baKsol_two` (`BA/KInduct.lean:88`). -/
theorem twK_ba (z : ℕ → ℂ) (n : ℕ) (hm : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) (t : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    twK (baFMz sz z) n t σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a', BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) t (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁ := by
  unfold twK; rw [twMB_ba z n hm]; rfl

end Twist

/-! ## 3b. The model-free lemmas (proofs T.2, T.3, A.2 of `docs/tickets/T2398-TL-proofs.md`) and the deterministic bound `twK_bound` -/

section TwistLemmas
variable {d : ℕ} {sz : Sizes d}

private theorem TwistPins_split_shift (n : ℕ) (c : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    split d (sz.L n) (sz.W n) (twShift n c x) = (c, (split d (sz.L n) (sz.W n) x).2) :=
  (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _

private theorem TwistPins_mem_blk (n : ℕ) {c : Zd d (sz.L n)} {x : Idx d (sz.L n) (sz.W n)} :
    x ∈ twBlk n c ↔ (split d (sz.L n) (sz.W n) x).1 = c := by
  simp [twBlk]

private theorem TwistPins_shift_of_mem (n : ℕ) {c : Zd d (sz.L n)} {x : Idx d (sz.L n) (sz.W n)}
    (hx : x ∈ twBlk n c) : twShift n c x = x := by
  apply split_injective d (sz.L n) (sz.W n)
  rw [TwistPins_split_shift]
  exact Prod.ext ((TwistPins_mem_blk n).1 hx).symm rfl

private theorem TwistPins_shift_shift (n : ℕ) {c₁ c₂ : Zd d (sz.L n)} {x : Idx d (sz.L n) (sz.W n)}
    (hx : x ∈ twBlk n c₁) : twShift n c₁ (twShift n c₂ x) = x := by
  apply split_injective d (sz.L n) (sz.W n)
  rw [TwistPins_split_shift, TwistPins_split_shift]
  exact Prod.ext ((TwistPins_mem_blk n).1 hx).symm rfl

private theorem TwistPins_shift_mem (n : ℕ) (c₂ : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    twShift n c₂ x ∈ twBlk n c₂ := by
  rw [TwistPins_mem_blk, TwistPins_split_shift]

/-- `w ↦ (c₂, o_w)` is a bijection `[c₁] → [c₂]`. -/
private theorem TwistPins_sum_shift {β : Type*} [AddCommMonoid β] (n : ℕ) (c₁ c₂ : Zd d (sz.L n))
    (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ w ∈ twBlk n c₁, F (twShift n c₂ w) = ∑ y ∈ twBlk n c₂, F y := by
  refine Finset.sum_nbij (twShift n c₂) (fun w _ => TwistPins_shift_mem n c₂ w) ?_ ?_ (fun _ _ => rfl)
  · intro w hw w' hw' h
    have hw1 := (TwistPins_mem_blk n).1 (Finset.mem_coe.1 hw)
    have hw2 := (TwistPins_mem_blk n).1 (Finset.mem_coe.1 hw')
    have h2 := congrArg (split d (sz.L n) (sz.W n)) h
    rw [TwistPins_split_shift, TwistPins_split_shift] at h2
    apply split_injective d (sz.L n) (sz.W n)
    exact Prod.ext (hw1.trans hw2.symm) (Prod.mk.inj h2).2
  · intro y hy
    have hy1 := (TwistPins_mem_blk n).1 (Finset.mem_coe.1 hy)
    refine ⟨(splitEquiv d (sz.L n) (sz.W n)).symm (c₁, (split d (sz.L n) (sz.W n) y).2), ?_, ?_⟩
    · rw [Finset.mem_coe, TwistPins_mem_blk]
      have : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (c₁, (split d (sz.L n) (sz.W n) y).2)) = (c₁, (split d (sz.L n) (sz.W n) y).2) := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
      rw [this]
    · apply split_injective d (sz.L n) (sz.W n)
      rw [TwistPins_split_shift]
      have : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (c₁, (split d (sz.L n) (sz.W n) y).2)) = (c₁, (split d (sz.L n) (sz.W n) y).2) := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
      rw [this]
      exact Prod.ext hy1.symm rfl

private theorem TwistPins_sum_twist {β : Type*} [AddCommMonoid β] (n : ℕ) (c₁ c₂ : Zd d (sz.L n))
    (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → β) :
    ∑ w ∈ twBlk n c₁, X (twShift n c₂ w) w = ∑ y ∈ twBlk n c₂, X y (twShift n c₁ y) := by
  rw [← TwistPins_sum_shift n c₁ c₂ (fun y => X y (twShift n c₁ y))]
  exact Finset.sum_congr rfl fun w hw => by rw [TwistPins_shift_shift n hw]

private theorem TwistPins_norm_inv_pow (n : ℕ) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  simp

/-- **`twFold`** (proofs T.2, (B.2)): Cauchy-Schwarz over the pairs `(x, w)`; `w ↦ (c₂, o_w)` is a bijection `[c₁] → [c₂]`. -/
theorem twFold_holds (sz : Sizes d) : twFold sz := by
  intro n X₁ X₂ a c₁ c₂
  set w : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  set S : ℂ := ∑ x ∈ twBlk n a, ∑ v ∈ twBlk n c₁, X₂ x v * X₁ (twShift n c₂ v) x with hSdef
  have h1 : ‖twLoopX n X₁ X₂ a c₁ c₂‖ = w ^ 2 * ‖S‖ := by
    unfold twLoopX; rw [norm_mul, norm_pow, TwistPins_norm_inv_pow]
  have hS : ‖S‖ ^ 2 ≤ (∑ x ∈ twBlk n a, ∑ v ∈ twBlk n c₁, ‖X₂ x v‖ ^ 2) *
      (∑ x ∈ twBlk n a, ∑ v ∈ twBlk n c₁, ‖X₁ (twShift n c₂ v) x‖ ^ 2) := by
    have h0 : ‖S‖ ≤ ∑ x ∈ twBlk n a, ∑ v ∈ twBlk n c₁, ‖X₂ x v‖ * ‖X₁ (twShift n c₂ v) x‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => (norm_mul _ _).le))
    calc ‖S‖ ^ 2 ≤ (∑ x ∈ twBlk n a, ∑ v ∈ twBlk n c₁, ‖X₂ x v‖ * ‖X₁ (twShift n c₂ v) x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h0 2
      _ = (∑ p ∈ twBlk n a ×ˢ twBlk n c₁, ‖X₂ p.1 p.2‖ * ‖X₁ (twShift n c₂ p.2) p.1‖) ^ 2 := by
          rw [Finset.sum_product]
      _ ≤ (∑ p ∈ twBlk n a ×ˢ twBlk n c₁, ‖X₂ p.1 p.2‖ ^ 2) *
            ∑ p ∈ twBlk n a ×ˢ twBlk n c₁, ‖X₁ (twShift n c₂ p.2) p.1‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by rw [Finset.sum_product, Finset.sum_product]
  have hA : ∑ x ∈ twBlk n a, ∑ v ∈ twBlk n c₁, ‖X₁ (twShift n c₂ v) x‖ ^ 2 =
      ∑ y ∈ twBlk n c₂, ∑ x ∈ twBlk n a, ‖X₁ y x‖ ^ 2 :=
    Finset.sum_comm.trans (TwistPins_sum_shift n c₁ c₂ (fun y => ∑ x ∈ twBlk n a, ‖X₁ y x‖ ^ 2))
  rw [h1]
  rw [hA] at hS
  unfold twSq
  rw [← hw]
  calc (w ^ 2 * ‖S‖) ^ 2 = (w ^ 2) ^ 2 * ‖S‖ ^ 2 := by ring
    _ ≤ (w ^ 2) ^ 2 * _ := mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by ring

private theorem TwistPins_sum_blk (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → ℂ) :
    ∑ a : Zd d (sz.L n), ∑ x ∈ twBlk n a, F x = ∑ x, F x :=
  Finset.sum_fiberwise Finset.univ (fun x => (split d (sz.L n) (sz.W n) x).1) F

/-- The core of `twWard`: `Y - Y' = 2iη P` and `Σ_z X₂ z y X₁ x z = P x y` give the Ward sum. -/
private theorem TwistPins_ward_core (n : ℕ) (η : ℝ) (hη : η ≠ 0)
    (Y Y' P X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (hP : ∀ x y, Y x y - Y' x y = (2 * (η : ℂ) * Complex.I) * P x y)
    (hX : ∀ x y, ∑ z, X₂ z y * X₁ x z = P x y) (c₁ c₂ : Zd d (sz.L n)) :
    ∑ a, twLoopX n X₁ X₂ a c₁ c₂ =
      (2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (η : ℂ))⁻¹ * (twTrP n Y c₁ c₂ - twTrP n Y' c₁ c₂) := by
  have hη' : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hη
  have h2 : (2 * (η : ℂ) * Complex.I) ≠ 0 := by simp [hη']
  have hP' : ∀ x y, P x y = (2 * (η : ℂ) * Complex.I)⁻¹ * (Y x y - Y' x y) := fun x y => by
    rw [hP]; field_simp
  unfold twLoopX
  rw [← Finset.mul_sum]
  have e1 : ∑ a : Zd d (sz.L n), ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, X₂ x w * X₁ (twShift n c₂ w) x =
      ∑ w ∈ twBlk n c₁, P (twShift n c₂ w) w := by
    rw [TwistPins_sum_blk n (fun x => ∑ w ∈ twBlk n c₁, X₂ x w * X₁ (twShift n c₂ w) x), Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => hX _ _
  rw [e1]
  simp only [hP', ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [TwistPins_sum_twist n c₁ c₂ Y, TwistPins_sum_twist n c₁ c₂ Y']
  unfold twTrP
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  field_simp

/-- **`twWard`** (proofs T.3, `n = 2`; `Σ_a E_a = W^{-d}`): both charges, from the two resolvent identities (2.53). -/
theorem twWard_holds (sz : Sizes d) : twWard sz := by
  intro n G η hη h1 h2 σ c₁ c₂
  have e1 : ∀ x y, G x y - G.conjTranspose x y = (2 * (η : ℂ) * Complex.I) * (G * G.conjTranspose) x y := fun x y => by
    have := congrFun (congrFun h1 x) y
    simpa using this
  have e2 : ∀ x y, G x y - G.conjTranspose x y = (2 * (η : ℂ) * Complex.I) * (G.conjTranspose * G) x y := fun x y => by
    have := congrFun (congrFun h2 x) y
    simpa using this
  have c1' : ∀ x y, twChg G true x y = G x y := fun x y => by simp [twChg]
  have c2' : ∀ x y, twChg G false x y = G.conjTranspose x y := fun x y => by simp [twChg, Matrix.conjTranspose_apply]
  have hY : twChg G true = G := funext fun x => funext fun y => c1' x y
  have hY' : twChg G false = G.conjTranspose := funext fun x => funext fun y => c2' x y
  cases σ
  · simp only [Bool.not_false]
    refine TwistPins_ward_core n η hη (twChg G true) (twChg G false) (G.conjTranspose * G) _ _ ?_ ?_ c₁ c₂
    · intro x y; rw [c1', c2']; exact e2 x y
    · intro x y; simp only [c1', c2', Matrix.mul_apply, mul_comm]
  · simp only [Bool.not_true]
    refine TwistPins_ward_core n η hη (twChg G true) (twChg G false) (G * G.conjTranspose) _ _ ?_ ?_ c₁ c₂
    · intro x y; rw [c1', c2']; exact e1 x y
    · intro x y; simp only [c1', c2', Matrix.mul_apply, mul_comm]

private theorem TwistPins_shift_comp (n : ℕ) (c₁ c₂ : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    twShift n c₂ (twShift n c₁ x) = twShift n c₂ x := by
  apply split_injective d (sz.L n) (sz.W n)
  rw [TwistPins_split_shift, TwistPins_split_shift, TwistPins_split_shift]

/-- `Tr(X₁ E_a M P_{c₁c₂}) = W^{-d} M^{(B)}_{ac₁} Tr(X₁ P_{ac₂})` for `M_{wγ} = 1[offsets equal] M^{(B)}_{[w][γ]}`: the subtracted term of `twCirc`. -/
private theorem TwistPins_circ_term (n : ℕ) (X₁ M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hM : ∀ w γ, M w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
      MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0) (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n X₁ M a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB a c₁ * twTrP n X₁ a c₂ := by
  unfold twLoopX twTrP
  have key : ∀ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, M x w * X₁ (twShift n c₂ w) x =
      MB a c₁ * X₁ (twShift n c₂ x) x := by
    intro x hx
    have hxa := (TwistPins_mem_blk n).1 hx
    rw [Finset.sum_eq_single (twShift n c₁ x)]
    · have hs := TwistPins_split_shift n c₁ x
      rw [hM, hs]
      simp [hxa, TwistPins_shift_comp]
    · intro w hw hne
      have hn : ¬ (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) w).2 := by
        intro h
        apply hne
        apply split_injective d (sz.L n) (sz.W n)
        rw [TwistPins_split_shift]
        exact Prod.ext ((TwistPins_mem_blk n).1 hw) h.symm
      rw [hM]; simp [hn]
    · intro h; exact absurd (TwistPins_shift_mem n c₁ x) h
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, TwistPins_sum_twist n a c₂ X₁]
  ring

/-- **`twCirc`** (proofs A.2, the circled/uncircled relation): `twLoopX` is linear in the second slot. -/
theorem twCirc_holds (sz : Sizes d) : twCirc sz := by
  intro n X₁ X₂ M MB hM a c₁ c₂
  rw [← TwistPins_circ_term n X₁ M MB hM a c₁ c₂]
  unfold twLoopX
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun w _ => by ring

end TwistLemmas

/-! The deterministic bound `twK_bound` -/

section TwistBound
variable {d L : ℕ} [NeZero L]

/-- `M(σ)` of the block Anderson model is translation invariant (`BAMB_shift`; `M(-) = M^*`). -/
private theorem TwistPins_Msigma_shift (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ (x + c) (y + c) = BAMsigma d L (BAMB d L g z m) σ x y := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, BAMB_shift]
  · exact BAMB_shift d L g z m x y c

/-- `Θ = (1 - tQ)⁻¹` is invariant under a permutation `e` of the labels fixing `Q`. -/
private theorem TwistPins_theta_perm (e : Zd d L ≃ Zd d L) (Q : Matrix (Zd d L) (Zd d L) ℂ)
    (hQ : ∀ x y, Q (e x) (e y) = Q x y) (t : ℝ) (x y : Zd d L) :
    PropThetaQ Q t (e x) (e y) = PropThetaQ Q t x y := by
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q).submatrix e e = 1 - (t : ℂ) • Q := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQ]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q) e e
  rw [hA] at h2
  unfold PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- Translation invariance of `Θ`: `Θ_t^{(s,s')}(x, y) = Θ_t^{(s,s')}(0, y - x)`. -/
private theorem TwistPins_theta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BATheta d L g E m t s s' x y = BATheta d L g E m t s s' 0 (y - x) := by
  have h := TwistPins_theta_perm (Equiv.addRight (-x)) (BAMss d L (BAMB d L g (E : ℂ) m) s s')
    (fun u v => by
      simp only [Equiv.coe_addRight, BAMss, Matrix.of_apply, TwistPins_Msigma_shift]) t x y
  simp only [Equiv.coe_addRight, add_neg_cancel, ← sub_eq_add_neg] at h
  exact h.symm

/-- `|M(σ)_{ab}| = |M^{(B)}_{ab}|` (`M(-) = (M^{(B)})^*`, `M^{(B)}` symmetric). -/
private theorem TwistPins_norm_sigma (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b‖ = ‖BAMB d L g (E : ℂ) m a b‖ := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.norm_conj]
    rw [BAMB_symm d L g (E : ℂ) m b a]
  · simp only [BAMsigma, ite_true]

/-- `|M(σ)_{ab}| ≤ 1`: the Ward row identity `Σ_b |M^{(B)}_{ab}|² = 1` (`BAMB_row_sq_real`). -/
private theorem TwistPins_M_le_one {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ : Bool) (x y : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ ≤ 1 := by
  rw [TwistPins_norm_sigma]
  have hrow := BAMB_row_sq_real d L g E m hr.1 x
  have hle : ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (f := fun b => ‖BAMB d L g (E : ℂ) m x b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ y)
  nlinarith [norm_nonneg (BAMB d L g (E : ℂ) m x y)]

/-- `Σ_a |Θ(a,b)| ≤ (1-t)⁻¹` from the left resolvent identity `Θ = 1 + t Q Θ` and `Σ_a |Q(a,c)| ≤ 1`. -/
private theorem TwistPins_col_of_resolvent {G : Type*} [Fintype G] [DecidableEq G] (Θ Q : Matrix G G ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hres : Θ = 1 + (t : ℂ) • (Q * Θ))
    (hQ : ∀ c, ∑ a, ‖Q a c‖ ≤ 1) (b : G) : ∑ a, ‖Θ a b‖ ≤ (1 - t)⁻¹ := by
  set R : ℝ := ∑ a, ‖Θ a b‖ with hR
  have hpt : ∀ a, ‖Θ a b‖ ≤ (if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Q a c‖ * ‖Θ c b‖ := by
    intro a
    have h := congrFun (congrFun hres a) b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Matrix.mul_apply] at h
    rw [h]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖(if a = b then (1 : ℂ) else 0)‖ = if a = b then (1 : ℝ) else 0 := by split_ifs <;> simp
    have h2 : ‖(t : ℂ) * ∑ c, Q a c * Θ c b‖ ≤ t * ∑ c, ‖Q a c‖ * ‖Θ c b‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) ht0
      exact Finset.sum_congr rfl fun c _ => norm_mul _ _
    rw [h1]
    linarith
  have hsum : R ≤ 1 + t * R := by
    calc R = ∑ a, ‖Θ a b‖ := rfl
      _ ≤ ∑ a, ((if a = b then (1 : ℝ) else 0) + t * ∑ c, ‖Q a c‖ * ‖Θ c b‖) := Finset.sum_le_sum fun a _ => hpt a
      _ = 1 + t * ∑ c, (∑ a, ‖Q a c‖) * ‖Θ c b‖ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul]
      _ ≤ 1 + t * ∑ c, 1 * ‖Θ c b‖ := by
          gcongr with c _
          exact hQ c
      _ = 1 + t * R := by simp [hR]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

/-- `Σ_a |Θ_t^{(s,s')}(a,b)| ≤ (1-t)⁻¹` for all four charge pairs: the left resolvent identity (`BATheta_resolvent`)
and `Σ_a |M^{(s,s')}_{ac}| = Σ_a K_{ac} = 1` (`BAMss_norm_eq_BAK`, `BAK_col_sum`). -/
private theorem TwistPins_theta_col_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (s s' : Bool) (b : Zd d L) :
    ∑ a, ‖BATheta d L g E m t s s' a b‖ ≤ (1 - t)⁻¹ := by
  refine TwistPins_col_of_resolvent (BATheta d L g E m t s s') (BAMss d L (BAMB d L g (E : ℂ) m) s s') ht0 ht1
    (BATheta_resolvent d L g κ E m hr t ht0 ht1 s s').1 (fun c => ?_) b
  simp only [BAMss_norm_eq_BAK]
  exact (BAK_col_sum d L g E m hr.1 c).le

/-- **The `Θ`-sums of `twK` (T.1 (i), (ii))** at the real-axis data `(g, E, m)` with `0 < g ≤ Λ`: for `d = k + 2`, `Cd` from `baProp5_holds`,
`C_M = c⁻¹ expC k c` from `BAMB_row_l1`: `|Σ_{a'} Θ(a,a') M_{σ₁}(c₂,a') M_{σ₂}(a',c₁)| ≤ Cd B_{t,0} C_M` and
`Σ_a |Σ_{a'} ...| ≤ (1-t)⁻¹ C_M`. -/
private theorem TwistPins_alg {k : ℕ} (hd : 3 ≤ k + 2) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      BAReal (k + 2) L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₁ σ₂ : Bool) (c₁ c₂ : Zd (k + 2) L),
        (∀ a, ‖∑ a', BATheta (k + 2) L g E m t σ₁ σ₂ a a' * BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a' *
            BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₂ a' c₁‖ ≤
          Cd * Bparam (k + 2) L g t 0 * ((BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ))) ∧
        ∑ a, ‖∑ a', BATheta (k + 2) L g E m t σ₁ σ₂ a a' * BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a' *
            BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₂ a' c₁‖ ≤
          (1 - t)⁻¹ * ((BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ)) := by
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := baProp5_holds (k + 2) Λ κ hd hΛ hκ
  refine ⟨Cd, hCd, fun L _ hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ c₁ c₂ => ?_⟩
  have hsup : ∀ x y, ‖BATheta (k + 2) L g E m t σ₁ σ₂ x y‖ ≤ Cd * Bparam (k + 2) L g t 0 := by
    intro x y
    rw [TwistPins_theta_shift]
    exact RBM.Loop.KLIndStepA_decay_le_zero (by omega) hCd.le hcd.le (y - x)
      (hbd L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (y - x))
  have hrow : ∑ a', ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ ≤
      (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ) := by
    simp only [TwistPins_norm_sigma]
    exact BAMB_row_l1 k L hL Λ g κ E m hΛ hg hgΛ hκ hr c₂
  have hterm : ∀ a a', ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a' * BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a' *
      BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₂ a' c₁‖ ≤
      ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖ * ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ := by
    intro a a'
    rw [norm_mul, norm_mul]
    exact mul_le_of_le_one_right (by positivity) (TwistPins_M_le_one hr σ₂ a' c₁)
  have hB : 0 ≤ Bparam (k + 2) L g t 0 := by unfold Bparam; positivity
  have ht1' : 0 ≤ (1 - t)⁻¹ := inv_nonneg.2 (by linarith)
  constructor
  · intro a
    calc _ ≤ ∑ a', ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖ * ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => hterm a a')
      _ ≤ ∑ a', (Cd * Bparam (k + 2) L g t 0) * ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ :=
          Finset.sum_le_sum fun a' _ => mul_le_mul_of_nonneg_right (hsup a a') (norm_nonneg _)
      _ = (Cd * Bparam (k + 2) L g t 0) * ∑ a', ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hrow (by positivity)
  · calc _ ≤ ∑ a, ∑ a', ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖ * ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ :=
          Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => hterm a a')
      _ = ∑ a', (∑ a, ‖BATheta (k + 2) L g E m t σ₁ σ₂ a a'‖) * ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun a' _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ a', (1 - t)⁻¹ * ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ :=
          Finset.sum_le_sum fun a' _ => mul_le_mul_of_nonneg_right (TwistPins_theta_col_le hr ht0 ht1 σ₁ σ₂ a') (norm_nonneg _)
      _ = (1 - t)⁻¹ * ∑ a', ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ₁ c₂ a'‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hrow ht1'

end TwistBound

section TwistFlow

/-- `B_{t,0}` at the flow coupling `g₀` against the coupling `g` of the pin: `g² ≤ c g₀²`, `1 ≤ c`, `t < 1` give `B(g₀) ≤ c B(g)`
(a copy of the private `KBound_bparam_comp`, `BA/KBound.lean:127`). -/
private theorem TwistPins_bparam_comp (d L : ℕ) {g g₀ t c : ℝ} (ht : t < 1) (hc : 1 ≤ c) (h : g ^ 2 ≤ c * g₀ ^ 2) :
    Bparam d L g₀ t 0 ≤ c * Bparam d L g t 0 := by
  have h1 : 0 < |1 - t| := abs_pos.2 (by linarith)
  have hA : 0 < g₀ ^ 2 + |1 - t| := by positivity
  have hB : 0 < g ^ 2 + |1 - t| := by positivity
  have hLd : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  have e1 : (g₀ ^ 2 + |1 - t|)⁻¹ ≤ c * (g ^ 2 + |1 - t|)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one, div_le_div_iff₀ hA hB]
    nlinarith [abs_nonneg (1 - t)]
  have e2 : ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤ c * ((L : ℝ) ^ d * |1 - t|)⁻¹ := by nlinarith
  unfold Bparam
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  nlinarith

/-- `t₀ = Im m / (Im m + Im z) ≥ κ/(κ+1)` on the chain domain (a copy of the private `KBound_t0_ge`, `BA/KBound.lean:143`). -/
private theorem TwistPins_t0_ge {z m : ℂ} {κ : ℝ} (hκ : 0 < κ) (hm : κ ≤ m.im) (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    κ / (κ + 1) ≤ BAt0 z m := by
  unfold BAt0
  have hm0 : 0 < m.im := lt_of_lt_of_le hκ hm
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `Im z_n > 0` on the chain domain (a copy of the private `KBound_zim_pos`, `BA/KBound.lean:152`). -/
private theorem TwistPins_zim_pos {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)) _
  linarith

/-- **The comparison of the couplings along a flow**: `(W^d)⁻¹ B_{t,0}(g₀_n) ≤ ((κ+1)/κ) · (W^{-d} B_{t,0}(g_n))` for every `n` and
`t < 1` (a copy of the private `KBound_B_le`, `BA/KBound.lean:160`). -/
private theorem TwistPins_B_le {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht : t < 1) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (BAflowLam0 sz z n) t 0 ≤ (κ + 1) / κ * sz.Bctl n t := by
  obtain ⟨hκm, -, hz1⟩ := hflow.2 n
  have hzim := TwistPins_zim_pos sz hflow n
  have ht0 := TwistPins_t0_ge hκ hκm hzim hz1
  have ht0' : 0 < BAflowT0 sz z n := BAt0_pos hzim (lt_of_lt_of_le hκ hκm)
  have hc : 1 ≤ (κ + 1) / κ := by rw [le_div_iff₀ hκ]; linarith
  have hg : sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2 := by
    have e : BAflowLam0 sz z n ^ 2 = BAflowT0 sz z n * sz.lam n ^ 2 := by
      unfold BAflowLam0; rw [mul_pow, Real.sq_sqrt ht0'.le]
    rw [e]
    have h1 : 1 ≤ (κ + 1) / κ * BAflowT0 sz z n := by
      have := mul_le_mul_of_nonneg_left ht0 (by positivity : 0 ≤ (κ + 1) / κ)
      calc (1 : ℝ) = (κ + 1) / κ * (κ / (κ + 1)) := by field_simp
        _ ≤ _ := this
    nlinarith [sq_nonneg (sz.lam n)]
  have hcomp := TwistPins_bparam_comp d (sz.L n) ht hc hg
  have hW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  unfold Sizes.Bctl
  calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((κ + 1) / κ * Bparam d (sz.L n) (sz.lam n) t 0) :=
        mul_le_mul_of_nonneg_left hcomp hW
    _ = _ := by ring

/-- **`twK_bound` is proved** (T.1 (i)-(ii), eventually in `n`): the constant is `C_d C_M (κ+1)/κ + C_M` with `C_d` from `baProp5_holds`
(`Λ = 𝔡⁻¹`) and `C_M = c⁻¹ expC k c` from `BAMB_row_l1` (`d = k + 2`); the window `0 < g₀_n ≤ 𝔡⁻¹` is `BAflow_lam0_window`, `B(g₀) ≤ ((κ+1)/κ) B(g)`
is `TwistPins_B_le`, and `Im m_F ≤ 1` is `BAself_im_le_one`. -/
theorem twK_bound_holds (d : ℕ) : twK_bound d := by
  intro hd κ ε 𝔡 hκ hε h𝔡
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨Cd, hCd, H⟩ := TwistPins_alg hd hΛ hκ
  have hc := BAct_rate_pos (k + 2) 𝔡⁻¹ κ (by omega) hΛ hκ
  have hCM : 0 < (BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC k (BAct_rate (k + 2) 𝔡⁻¹ κ) := by unfold expC; positivity
  set CM : ℝ := (BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC k (BAct_rate (k + 2) 𝔡⁻¹ κ) with hCMdef
  have hκ1 : 0 < (κ + 1) / κ := by positivity
  refine ⟨Cd * CM * ((κ + 1) / κ) + CM, by positivity, ?_⟩
  intro 𝔠 sz z hflow t ht0 htT
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro σ c₁ c₂
  have hreal := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hzim := TwistPins_zim_pos sz hflow n
  obtain ⟨hκm, -, hz1⟩ := hflow.2 n
  have hmpos : 0 < (BAm (k + 2) (sz.L n) (sz.lam n) (z n)).im := lt_of_lt_of_le hκ hκm
  have ht1 : t n < 1 := lt_of_le_of_lt (htT n) (BAt0_lt_one hzim hmpos)
  have hmF : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := hreal.1.1
  have hL3 := sz.three_le_L n
  have hall := H (sz.L n) hL3 (BAflowLam0 sz z n) hn.1 hn.2 (BAflowEs sz z n) _ hreal (t n) (ht0 n) ht1 (σ 0) (σ 1) c₁ c₂
  have hB := TwistPins_B_le hκ sz hflow n ht1
  have hBc : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
  have hWi : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ := by positivity
  have hnorm : ∀ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ = (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ *
      ‖∑ a', BATheta (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) (σ 0) (σ 1) a a' *
        BAMsigma (k + 2) (sz.L n) (BAMB (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
        BAMsigma (k + 2) (sz.L n) (BAMB (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁‖ := by
    intro a
    rw [twK_ba z n hmF (t n) σ a c₁ c₂, norm_mul, TwistPins_norm_inv_pow]
  refine ⟨fun a => ?_, ?_⟩
  · rw [hnorm a]
    calc (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * _ ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * (Cd * Bparam (k + 2) (sz.L n) (BAflowLam0 sz z n) (t n) 0 * CM) :=
          mul_le_mul_of_nonneg_left (hall.1 a) hWi
      _ = Cd * CM * ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) (sz.L n) (BAflowLam0 sz z n) (t n) 0) := by ring
      _ ≤ Cd * CM * ((κ + 1) / κ * sz.Bctl n (t n)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ (Cd * CM * ((κ + 1) / κ) + CM) * sz.Bctl n (t n) := by nlinarith [mul_nonneg hCM.le hBc]
  · have heta : (baFMz sz z).eta n (t n) = (1 - t n) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl
    have him1 : (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≤ 1 :=
      BAself_im_le_one (z := (BAflowEs sz z n : ℂ)) (by simp) hreal.1
    have h1t : 0 < 1 - t n := by linarith
    have hsum : ∑ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ((1 - t n)⁻¹ * CM) := by
      calc ∑ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ = (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ∑ a, ‖∑ a', BATheta (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) (σ 0) (σ 1) a a' *
        BAMsigma (k + 2) (sz.L n) (BAMB (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
        BAMsigma (k + 2) (sz.L n) (BAMB (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁‖ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => hnorm a
        _ ≤ _ := mul_le_mul_of_nonneg_left hall.2 hWi
    have hWp : 0 < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
      have := sz.W_pos n
      positivity
    have hkey : (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ((1 - t n)⁻¹ * CM) ≤ CM * ((((sz.W n : ℕ) : ℝ) ^ (k + 2)) * ((1 - t n) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im))⁻¹ := by
      set im := (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im
      have e : (((sz.W n : ℕ) : ℝ) ^ (k + 2) * ((1 - t n) * im))⁻¹ = (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * (1 - t n)⁻¹ * im⁻¹ := by
        rw [mul_inv, mul_inv, mul_assoc]
      rw [e]
      have : (1 : ℝ) ≤ im⁻¹ := (one_le_inv₀ hmF).2 him1
      have h0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * (1 - t n)⁻¹ * CM := by positivity
      nlinarith
    rw [heta]
    calc _ ≤ _ := hsum
      _ ≤ _ := hkey
      _ ≤ (Cd * CM * ((κ + 1) / κ) + CM) * ((((sz.W n : ℕ) : ℝ) ^ (k + 2)) * ((1 - t n) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im))⁻¹ := by
          have hq : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ (k + 2)) * ((1 - t n) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im))⁻¹ := by positivity
          nlinarith [mul_nonneg (mul_nonneg hCd.le hCM.le) hκ1.le, mul_nonneg (mul_nonneg (mul_nonneg hCd.le hCM.le) hκ1.le) hq]

end TwistFlow

/-! ## 4. The instances (`d = 3`, `sz0`: `L = 4`, `W = 32`, `λ = 1/64`, `flow_sz0`; `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0`).  Other gates' pins stay hypotheses. -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.MFixedPointInst
local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- Every deterministic hypothesis of a `BATwFrame` statement at `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`, `sz0`, `s ≡ 1/2`, `t ≡ 2/3`, regime `STAny`. -/
private theorem TwistPins_frame_inst {Q : ∀ sz : Sizes 3, FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (h : BATwFrame 3 STAny Q) {Cd : ℝ} (hC : 0 < Cd)
    (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) Cd) : Q sz0 (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) := by
  obtain ⟨c, hc, -, H⟩ := h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hC
  exact H (1 / 6) sz0 zSeq flow_sz0 _ _ (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) trivial
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) hc) hS

variable {Cd : ℝ} (hC : 0 < Cd) (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) Cd)
include hC hS

/-- T.12' (needs TL2 at `s`), T.11 (i)-(v). -/
example (h : BATwistLoopStep 3 STAny) := TwistPins_frame_inst h hC hS
example (h : BATwistSrc1 3 STAny) := TwistPins_frame_inst h hC hS
example (h : BATwistSrc2 3 STAny) := TwistPins_frame_inst h hC hS
example (h : BATwistSrc3 3 STAny) := TwistPins_frame_inst h hC hS
example (h : BATwistSrc4 3 STAny) := TwistPins_frame_inst h hC hS
example (h : BATwistSrc5 3 STAny) := TwistPins_frame_inst h hC hS
omit hC hS

/-- TL1 producer (T.7), base case, TL-V (the chain statement and its output): applied at the datum, with the owed pins as hypotheses. -/
example (h : BATwistAvgProd 3) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hM : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    BATwistAvgLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le) hA hM
example (h : BATwistLoopBase 3) (hG : STG0M (baFMz sz0 zSeq)) : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 0) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq flow_sz0 hG
example (h : BAMainIndTL 3 STAny) (hyp : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧
    STDecayStronggL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ STLocalMaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧
    STExp2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) ∧ BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    let C := baFMz sz0 zSeq; let t : ℕ → ℝ := fun _ => 2 / 3
    STLKgL C μ0 t ∧ STLmaxgL C μ0 t ∧ STDecaygL C μ0 t ∧ STExp2gL C μ0 t ∧ STLocalEntrygL C μ0 t ∧ STDecayStronggL C μ0 t ∧ BATwistLoopLaw C μ0 t := by
  obtain ⟨c, hc, -, H⟩ := h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  exact H (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (fun _ => by norm_num)
    (fun n => t0_sz0 n) trivial hyp (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) hc)
example (h : BAMLOutTL 3) : let C := baFMz sz0 zSeq; STLKgL C μ0 (fun _ => 1 / 2) ∧ STLmaxgL C μ0 (fun _ => 1 / 2) ∧ STDecaygL C μ0 (fun _ => 1 / 2) ∧
    STExp2gL C μ0 (fun _ => 1 / 2) ∧ STLocalEntrygL C μ0 (fun _ => 1 / 2) ∧ BATwistLoopLaw C μ0 (fun _ => 1 / 2) :=
  h le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le)
example (h : BAChainTL 3) (hm : BAMainIndTL 3 STAny) (hh : STHorizonG 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => BAflowT0 sz z))
    (hb : STBaseG 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz) (ht : BATwistLoopBase 3)
    (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) : BAMLOutTL 3 := h hm hh hb ht hG

/-- D3, O3 (`c₂ ≠ c₁`), at the eventual form of `twK_bound` (Amend 1): `twK_bound_holds 3` at the datum `sz0` (`flow_sz0`, `s ≡ 1/2`) with `σ = (-,+)`
and a pair `c₂ ≠ c₁` of blocks (`c₁ = 0`, `c₂ = (1,0,0)`): for every `n` of the window (an eventual set; non-vacuous since `atTop` on `ℕ` is `NeBot`),
both bounds with the constant. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∃ c₁ c₂ : Zd 3 (sz0.L n), c₂ ≠ c₁ ∧
    (∀ a, ‖twK (baFMz sz0 zSeq) n (1 / 2) ![false, true] a c₁ c₂‖ ≤ C * sz0.Bctl n (1 / 2)) ∧
    ∑ a, ‖twK (baFMz sz0 zSeq) n (1 / 2) ![false, true] a c₁ c₂‖ ≤ C * ((((sz0.W n : ℕ) : ℝ) ^ 3) * (baFMz sz0 zSeq).eta n (1 / 2))⁻¹ := by
  obtain ⟨C, hC, hall⟩ := twK_bound_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hall (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)] with n hn
  have : Fact (1 < sz0.L n) := ⟨by have := sz0.three_le_L n; omega⟩
  exact ⟨0, ![1, 0, 0], fun hh => by simpa using congrFun hh 0, (hn ![false, true] 0 ![1, 0, 0]).1, (hn ![false, true] 0 ![1, 0, 0]).2⟩

/-- Instances of `twTr_eq`, `twMB_ba`, `twK_ba` at the datum `sz0`, `n = 0`, `t = 1/2`, `σ = (-,+)`, blocks `a = 0`, `c₁ = 0`, `c₂ = (1,0,0)`; the hypothesis
`Im m_F > 0` is `BAmF_sz0_im_pos`. -/
example (t : ℝ) (ω : (sz0).SeqΩ) (c₁ c₂ : Zd 3 (sz0.L 0)) :
    twTr (baFMz sz0 zSeq) 0 t ω c₁ c₂ = twTrP 0 ((baFMz sz0 zSeq).GM 0 t ω) c₂ c₁ := twTr_eq (baFMz sz0 zSeq) 0 t ω c₁ c₂
example : twMB (baFMz sz0 zSeq) 0 = BAMB 3 (sz0.L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0 : ℂ)
    (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0) := twMB_ba zSeq 0 (BAmF_sz0_im_pos 0)
example := twK_ba (sz := sz0) zSeq 0 (BAmF_sz0_im_pos 0) (1 / 2) ![false, true] 0 0 ![1, 0, 0]

/-- `Tr(X P_{cc})` of a scalar matrix `r · 1` is `r` (`c₁ = c₂`: `twShift n c w = w` on `[c]`, `|[c]| = W^d`). -/
private theorem TwistPins_trP_diag {d : ℕ} {sz : Sizes d} (n : ℕ) (c : Zd d (sz.L n)) (r : ℂ) :
    twTrP n (fun x y : Idx d (sz.L n) (sz.W n) => if x = y then r else 0) c c = r := by
  unfold twTrP
  rw [Finset.sum_congr rfl (fun w hw => by rw [TwistPins_shift_of_mem n hw]; simp only [ite_true] : ∀ w ∈ twBlk n c,
    (fun x y : Idx d (sz.L n) (sz.W n) => if x = y then r else 0) w (twShift n c w) = r)]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (twBlk n c).card = (sz.W n) ^ d := card_Iblk d (sz.L n) (sz.W n) c
  rw [hc]
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  push_cast
  field_simp

/-- D3, O4 (non-vacuity of `twWard`): the hypotheses (2.53) hold at `G = i · 1` (`H = 0`, `z = i`), `η = 1`, and for both charges the sum is `W^{-d} ≠ 0`
at `c₁ = c₂ = 0`. -/
example : (∑ a, twLoopX 0 (twChg (Complex.I • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) true)
    (twChg (Complex.I • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) false) a 0 0 = (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹) ∧
    (∑ a, twLoopX 0 (twChg (Complex.I • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) false)
    (twChg (Complex.I • (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)) true) a 0 0 = (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹) ∧
    (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ ≠ 0 := by
  set G : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := Complex.I • 1 with hG
  have hW : ((sz0.W 0 : ℕ) : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz0.W_pos 0).ne')
  have h1 : G - G.conjTranspose = (2 * ((1 : ℝ) : ℂ) * Complex.I) • (G * G.conjTranspose) := by
    simp [hG, Matrix.conjTranspose_smul, smul_smul]; rw [mul_smul, two_smul]
  have h2 : G - G.conjTranspose = (2 * ((1 : ℝ) : ℂ) * Complex.I) • (G.conjTranspose * G) := by
    simp [hG, Matrix.conjTranspose_smul, smul_smul]; rw [mul_smul, two_smul]
  have eT : twChg G true = fun x y => if x = y then Complex.I else 0 := by
    funext x y; simp [twChg, hG, Matrix.one_apply]
  have eF : twChg G false = fun x y => if x = y then -Complex.I else 0 := by
    funext x y
    by_cases hxy : x = y
    · subst hxy; simp [twChg, hG]
    · have hyx : y ≠ x := fun h => hxy h.symm
      simp [twChg, hG, hxy, hyx]
  have hS : ∀ σ : Bool, ∑ a, twLoopX 0 (twChg G σ) (twChg G (!σ)) a 0 0 = (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ := by
    intro σ
    rw [twWard_holds sz0 0 G 1 one_ne_zero h1 h2 σ 0 0, eT, eF, TwistPins_trP_diag, TwistPins_trP_diag]
    push_cast
    field_simp
    ring
  exact ⟨hS true, hS false, inv_ne_zero hW⟩

/-- Non-vacuity of `twCirc`: the hypothesis (`BAMfine_eq`: the carrier's `M` ties offsets, `MB = M^{(B)}`) holds at `n = 0` of the datum `sz0`. -/
example (X₁ X₂ : Idx 3 (sz0.L 0) (sz0.W 0) → Idx 3 (sz0.L 0) (sz0.W 0) → ℂ) (a c₁ c₂ : Zd 3 (sz0.L 0)) :=
  twCirc_holds sz0 0 X₁ X₂ ((baFMz sz0 zSeq).M 0) (BAMB 3 (sz0.L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0 : ℂ) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0))
    (fun w γ => BAMfine_eq sz0 _ _ 0 (BAmF_sz0_im_pos 0) w γ) a c₁ c₂

/-- `twFold` at a twisted nonzero datum: `X₂ x w = 1[x = (a, o_w)]` (the block shift `[c₁] → [a]`), `X₁ y x = 1[y = (c₂, o_x)]` (`[a] → [c₂]`);
for all blocks `a, c₁, c₂` (in particular pairwise distinct ones) the loop is `W^{-d}`. -/
private theorem TwistPins_loopX_perm {d : ℕ} {sz : Sizes d} (n : ℕ) (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n (fun y x : Idx d (sz.L n) (sz.W n) => if y = twShift n c₂ x then (1 : ℂ) else 0)
      (fun x w : Idx d (sz.L n) (sz.W n) => if x = twShift n a w then (1 : ℂ) else 0) a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ := by
  unfold twLoopX
  rw [Finset.sum_comm]
  have key : ∀ w ∈ twBlk n c₁, ∑ x ∈ twBlk n a, (if x = twShift n a w then (1 : ℂ) else 0) *
      (if twShift n c₂ w = twShift n c₂ x then (1 : ℂ) else 0) = 1 := by
    intro w _
    rw [Finset.sum_eq_single (twShift n a w)]
    · simp [TwistPins_shift_comp]
    · intro x _ hx; simp [hx]
    · intro h; exact absurd (TwistPins_shift_mem n a w) h
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul]
  have hc : (twBlk n c₁).card = (sz.W n) ^ d := card_Iblk d (sz.L n) (sz.W n) c₁
  rw [hc]
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  push_cast
  field_simp

/-- `twFold` at pairwise distinct blocks `a = 0`, `c₁ = (1,0,0)`, `c₂ = (2,0,0)` (`L = 4`) and the twisted nonzero datum of `TwistPins_loopX_perm`: the left side
is `W^{-d} > 0`. -/
example : (0 : Zd 3 (sz0.L 0)) ≠ ![1, 0, 0] ∧ (![1, 0, 0] : Zd 3 (sz0.L 0)) ≠ ![2, 0, 0] ∧ (0 : Zd 3 (sz0.L 0)) ≠ ![2, 0, 0] ∧
    0 < ‖twLoopX 0 (fun y x : Idx 3 (sz0.L 0) (sz0.W 0) => if y = twShift 0 ![2, 0, 0] x then (1 : ℂ) else 0)
      (fun x w : Idx 3 (sz0.L 0) (sz0.W 0) => if x = twShift 0 0 w then (1 : ℂ) else 0) 0 ![1, 0, 0] ![2, 0, 0]‖ ∧
    ‖twLoopX 0 (fun y x : Idx 3 (sz0.L 0) (sz0.W 0) => if y = twShift 0 ![2, 0, 0] x then (1 : ℂ) else 0)
      (fun x w : Idx 3 (sz0.L 0) (sz0.W 0) => if x = twShift 0 0 w then (1 : ℂ) else 0) 0 ![1, 0, 0] ![2, 0, 0]‖ ^ 2 ≤
    twSq 0 (fun y x : Idx 3 (sz0.L 0) (sz0.W 0) => if y = twShift 0 ![2, 0, 0] x then (1 : ℂ) else 0) ![2, 0, 0] 0 *
      twSq 0 (fun x w : Idx 3 (sz0.L 0) (sz0.W 0) => if x = twShift 0 0 w then (1 : ℂ) else 0) 0 ![1, 0, 0] := by
  refine ⟨by decide, by decide, by decide, ?_, twFold_holds sz0 0 _ _ 0 ![1, 0, 0] ![2, 0, 0]⟩
  rw [TwistPins_loopX_perm]
  have hW : ((sz0.W 0 : ℕ) : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz0.W_pos 0).ne')
  exact norm_pos_iff.2 (inv_ne_zero hW)

/-- Non-degeneracy of `twCirc`: at `X₁ = 1`, `a = c₁ = c₂ = 0` the correction term `W^{-d} M^{(B)}_{00} Tr(X₁ P_{00}) = W^{-d} m_F ≠ 0` (`M^{(B)}_{aa} = m`,
`Im m_F > 0`), so the circled and uncircled loops differ. -/
example (X₂ : Idx 3 (sz0.L 0) (sz0.W 0) → Idx 3 (sz0.L 0) (sz0.W 0) → ℂ) :
    twLoopX 0 (fun x y : Idx 3 (sz0.L 0) (sz0.W 0) => if x = y then (1 : ℂ) else 0) (fun x y => X₂ x y - (baFMz sz0 zSeq).M 0 x y) 0 0 0 ≠
      twLoopX 0 (fun x y : Idx 3 (sz0.L 0) (sz0.W 0) => if x = y then (1 : ℂ) else 0) X₂ 0 0 0 := by
  have hreal := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0
  have h := twCirc_holds sz0 0 (fun x y : Idx 3 (sz0.L 0) (sz0.W 0) => if x = y then (1 : ℂ) else 0) X₂ ((baFMz sz0 zSeq).M 0)
    (BAMB 3 (sz0.L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0 : ℂ) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0))
    (fun w γ => BAMfine_eq sz0 _ _ 0 (BAmF_sz0_im_pos 0) w γ) 0 0 0
  rw [h, TwistPins_trP_diag, BAMB_diag_eq _ _ _ _ _ hreal.1 0]
  intro hh
  have h0 := sub_eq_self.1 hh
  have hW : ((sz0.W 0 : ℕ) : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz0.W_pos 0).ne')
  have hm : BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 ≠ 0 := fun h' => by
    have := BAmF_sz0_im_pos 0; rw [h'] at this; simp at this
  simp [hW, hm] at h0

/-- T.10 at the flow point `Pf` of `(L, g) = (4, 1/2)` (`BA/MFixedPoint.lean:877-885`: `0 < Pf.g0 ≤ 1/2`, `BAReal`, `κ = Im Pf.m0`, `Λ = 1`): (a); (b) with `A = δ_0`, `W = 16`,
`ε = 1/2`, `D = 2`, `v = 0`, `u = 1/2`; (c) is merged; (d) with `A = 1` at `v = 1 - g₀²/16 < u = 1 - g₀²/32`. -/
private def TwistPins_Pf : FlowPt 4 (1 / 2) := (exists_flowPt 4 (g := 1 / 2) (by norm_num)).some
example (h : BATwKerA 3 1 TwistPins_Pf.m0.im) (A : Zd 3 4 → ℂ) : ‖BAuKer 3 4 TwistPins_Pf.g0 TwistPins_Pf.E TwistPins_Pf.m0 0 (1 / 2) false true *ᵥ A‖ ≤ (1 - 0) / (1 - 1 / 2) * ‖A‖ :=
  h le_rfl one_pos TwistPins_Pf.real.1.1 4 (by norm_num) TwistPins_Pf.g0 TwistPins_Pf.g0_pos (TwistPins_Pf.g0_le.trans (by norm_num)) TwistPins_Pf.E TwistPins_Pf.m0 TwistPins_Pf.real false true 0 (1 / 2) le_rfl
    (by norm_num) (by norm_num) A
example : BAEKSameRow 3 1 TwistPins_Pf.m0.im := baEKSameRow_holds 3 1 TwistPins_Pf.m0.im
example (h : BATwKerFar 3 1 TwistPins_Pf.m0.im) : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ A : Zd 3 4 → ℂ, A ≠ 0 ∧ ‖BAuKer 3 4 TwistPins_Pf.g0 TwistPins_Pf.E TwistPins_Pf.m0 0 (1 / 2) false true *ᵥ A‖ ≤
    (1 + C₁ * (16 : ℝ) ^ (2 * (1 / 2 : ℝ)) * ((TwistPins_Pf.g0 ^ 2 + |1 - 0|) / (TwistPins_Pf.g0 ^ 2 + |1 - 1 / 2|))) * ‖A‖ + (16 : ℝ) ^ (-2 + 1 : ℝ) := by
  obtain ⟨C₁, hC₁, H⟩ := h le_rfl one_pos TwistPins_Pf.real.1.1
  have hg := TwistPins_Pf.g0_pos; have hg2 := TwistPins_Pf.g0_le
  refine ⟨C₁, hC₁, fun x => if x = 0 then 1 else 0, fun hA => by simpa using congrFun hA 0, H 4 (by norm_num) TwistPins_Pf.g0 hg (hg2.trans (by norm_num)) 16 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0 (1 / 2) le_rfl (by norm_num) (by norm_num; nlinarith) (by norm_num) TwistPins_Pf.E TwistPins_Pf.m0 TwistPins_Pf.real false true 0 _ ?_⟩
  intro b hb
  by_cases h0 : b = 0
  · subst h0
    have h1 := one_le_ellT (L := 4) (g := TwistPins_Pf.g0) (t := 0) (by norm_num)
    have h2 : (1 : ℝ) ≤ 16 ^ (1 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    simp [zdistD] at hb; nlinarith
  · simp [h0]
example (h : BATwKerZero 3 1 TwistPins_Pf.m0.im) : ∃ C : ℝ, 0 < C ∧ (open scoped Matrix.Norms.Operator in
    ‖projMat 3 4 * BAuKer 3 4 TwistPins_Pf.g0 TwistPins_Pf.E TwistPins_Pf.m0 (1 - TwistPins_Pf.g0 ^ 2 / 16) (1 - TwistPins_Pf.g0 ^ 2 / 32) false true‖) ≤ C ∧
    1 - TwistPins_Pf.g0 ^ 2 / 16 < 1 - TwistPins_Pf.g0 ^ 2 / 32 := by
  obtain ⟨C, hC, H⟩ := h le_rfl one_pos TwistPins_Pf.real.1.1 1 one_pos
  have hg := TwistPins_Pf.g0_pos; have hg2 := TwistPins_Pf.g0_le
  have hp : 0 < TwistPins_Pf.g0 ^ 2 := by positivity
  exact ⟨C, hC, H 4 (by norm_num) TwistPins_Pf.g0 hg (hg2.trans (by norm_num)) TwistPins_Pf.E TwistPins_Pf.m0 TwistPins_Pf.real false true _ _ (by nlinarith)
    (by norm_num) (by linarith) (by linarith), by linarith⟩

example (h : BATwistZeroMode 3) := h le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq flow_sz0 (fun _ => 1 / 2)
  (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) 0 ![false, true] (by simp) 0 ![1, 0, 0]

end Inst

end RBM.BA

end
