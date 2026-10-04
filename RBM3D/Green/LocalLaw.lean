/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.Pins
import RBM3D.Green.CondDom
import RBM3D.Green.EntryDom
import RBM3D.Green.FlucVanish
import RBM3D.Induction.PerTimeCalc

/-!
# The deterministic pins of `lem_GbEXP`, the local law at a deterministic control (ST-1, S1-27)

Ticket T2108.  Port of `RBM2D/Green/AvgPins.lean` (567 kept of 736 lines) and
`RBM2D/Green/LocalLaw.lean` (352 of 378) at RBM2D commit `c9a24cf`, to `d ≥ 3`, with the renaming
rules R1-R3 of `docs/tickets/ST1-COMMON.md` (`d : Sizes` becomes `sz : Sizes d`, `Z2 L`/`Idx L W`
become `Zd d L`/`Idx d L W`, `W²`, `W⁻²` become `W^d`, `W^{-d}`) on the merged vocabulary of
`RBM3D/Green/Pins.lean`.  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`
(`3_5:line`): `lem_GbEXP` (`3_5:14`), `(def_asGMc)` (`3_5:16`), `(GiiGEX)` (`3_5:21`), `(GijGEX)`
(`3_5:24`), `(initialGT2)` (`3_5:28-30`; the window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` is at `3_5:27`),
`(GavLGEX)` (`3_5:33`); the proof is "that of Lemma 4.1 in [YY_25]" (`3_5:37`).

The route (RBM2D T2127): for `Ψ' = max(Ψ, W^{-d/2})`, `AsGMcSeq` and `LoopDetSeq Ψ'` give
`LocalLawDetSeq Ψ'` (`localLawDetThm`), then `FixedTimeFASeq Ψ'` (pin FA) and `IBPDetSeq Ψ'` (pin
IBP), then `GavLDetSeq Ψ'` (`avgBoundDetThm`), then `GavLDetSeq Ψ` by the floor lemma
(`loopFloorThm`); the composition is `gbEXPV3Theorem_of_parts`.

## Contents (namespace `RBM.Green`)

1. vocabulary: `condDiagBlk`, `LocalLawDetSeq`, `IBPDet`, `FARowDet`, `FABlkDet`,
   `FixedTimeFASeq`, `IBPDetSeq`, `asGMcSeq_iff`;
2. the pins `LocalLawDetThm d`, `FixedTimeFAThm d`, `IBPDetThm d` (open: S1-28, S1-29, S1-30),
   `AvgBoundDetThm d`, `LoopFloorThm d`, `GavLDetFloorThm d`, `GavLDetThm d`;
3. the wiring: `gbEXPV3Theorem_of_gavLDetThm`, `loopDetSeq_mono`, `gavLDetThm_of_floor`,
   `gavLDetFloorThm_of_parts`, `gbEXPV3Theorem_of_parts`;
4. `LocalLaw_gexRHS_le_maxLoopPM` (`gexRHS ≤ 9^d max𝓛 + W^{-d}`), the calculus, `localLawDetThm`;
5. `avgBoundDetThm`, `loopFloorThm`, `gbEXPV3Theorem_of_ports`, `LocalLaw_gbEXPV3Theorem_of_fa_ibp`;
6. the extreme inputs `t ≡ 0`, `W ≡ 1`, `t → 1`;
7. compiled nonempty instances at `d = 3`, and the compiled counterexample
   `LocalLaw_loopFloor_literal_false` to the literal floor of RBM2D.

## Differences from RBM2D (every other ported statement equals RBM2D's after the renaming)

* The pins take `d : ℕ` as a parameter and `∀ sz : Sizes d`, in the binder order of the merged
  `GbEXPV3Theorem d` (`κ 𝔠 𝔡 δ`, positivity, `sz.Admissible 𝔠 𝔡`); RBM2D's
  `SizeTendsto d → Bandwidth d 𝔠` is `sz.Admissible 𝔠 𝔡` (R1; DECISIONS §22, D39) and `𝔡` is new.
* **The floor** `W⁻¹ ≤ Ψ` of RBM2D (the paper's `W^{-d/2} ≤ Ψ` of `3_5:27` at `d = 2`) is the
  paper's `W^{-d/2} ≤ Ψ` (paper-delta candidate `T2108a`), and `LoopFloorThm d` concludes
  `W^{-d} ≤ 4 N^ε Ψ²` (RBM2D `(W⁻¹)² ≤ 4 N^ε Ψ²`, the `W⁻²`-type of rule R3).  The literal port
  is false at `d = 3`: `LocalLaw_loopFloor_literal_false` (section 9) is a compiled counterexample
  at `sz0`, `t ≡ 0`.  The reduction `Ψ' = max(Ψ, floor)` of `gavLDetThm_of_floor` needs
  `floor² ≤ 4 N^ε Ψ²`, which the only lower bound `W^{-d} ≤ 4 max𝓛` (`inv_Wd_le_maxLoopPM`) gives
  for `floor = W^{-d/2}` and not for `W⁻¹`.
* The near set of `(GijGEX)` is the `L^∞` ball `{zdistInf ≤ 1}` of the merged `gexRHS`: it has at
  most `3^d` points (RBM2D: the `L¹` ball, 5 points), so `gexRHS ≤ 9^d max𝓛 + W^{-d}` (RBM2D
  `25`) and the absorption threshold is `9^d + 1` (RBM2D `26`); `LocalLaw_mem_sbSupport` (false for
  `zdistInf`: `(1,1,0)`) is replaced by the injection into `{0,1,-1}^d`; `hL : 3 ≤ L` of
  `LocalLaw_gexRHS_le_maxLoopPM` is not needed and is dropped.
* `hd : 3 ≤ d` (`giiSeq_of_asGMc`, `norm_avgErr_le`) is a hypothesis of `localLawDetThm`,
  `avgBoundDetThm`, `gbEXPV3Theorem_of_gavLDetThm`, `_of_parts`, `_of_ports`,
  `LocalLaw_gbEXPV3Theorem_of_fa_ibp`;
  `gavLDetThm_of_floor` takes `2 ≤ d` (`W^{-d/2} ≤ W⁻¹`); `loopFloorThm` takes none.
* The fine entries are on `Idx d L W` in the merged `offSq`, `diagSq`, so RBM2D's bridge
  `step2Local_llErrMat_eq` and the reindexing along `splitEquiv` of the off-diagonal part are not
  needed; the stability constant of `avgBoundDetThm` is the `n`-independent `Kstab3 d 𝔡⁻¹ κ`
  (RBM2D `Kstab2 κ L_n`).
* Dropped: `AvgPins_one_le_size` (merged `Sizes.one_le_size`), `llErrMat_time_zero` (merged,
  `Pins.lean`), `LocalLaw_mem_sbSupport` (false for `zdistInf`), `LocalLaw_card_le` (merged shape:
  `localLaw_card_Zd_sq_le`), the `Kstab2` helpers `eventually_Kstab2_le_rpow'`,
  `eventually_one_add_two_kstab2_le'`, `W_le_size'` (`Kstab3` does not depend on `n`), RBM2D's
  `AvgPinsCheck` instance namespace (replaced by the examples of section 9), and the bridge
  `step2Local_llErrMat_eq` of `Path/Step2Local` (the merged `offSq`, `diagSq` are on `Idx`; no ST-2
  file is imported).  The private copies of `EntryDom` helpers (`tendsto_size_of'`,
  `highProb_of_perTime'`, `maxLoop_dom_of_loopDet'`, the cardinalities) are re-proved here.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Loop
open scoped NNReal ENNReal

/-! ## 1. Vocabulary -/

section Vocab

variable {d : ℕ} (sz : Sizes d)

/-- `E_k(G_kk - m)` at the block-product index `k`: `condRow` (`Green/FlucVanish.lean`) integrates
out row `k` of the fine lattice, `k` read through `splitEquiv`.  This is the `x` of the merged
`avg_bound_stochDom`.  RBM2D `condDiagBlk` (`Green/AvgPins.lean:61`). -/
def condDiagBlk (E t : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) (k : Vtx d (sz.L n) (sz.W n)) : ℂ :=
  condRow sz n ((splitEquiv d (sz.L n) (sz.W n)).symm k)
    (fun ω' => greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω') true k k -
      mE (E n)) ω

/-- **Local law at a deterministic scale `Ψ`**: `max_{i,j} |(G_t - m)_{ij}| ≺ Ψ`, per time, entries
of the fine lattice (`llErrMat`).  [YY_25] proof of (`GavLGEX`), `Acta:4564`.  `AsGMcSeq sz E t c`
is this at `Ψ = W^{-c}` (`asGMcSeq_iff`).  RBM2D `LocalLawDetSeq` (`Green/AvgPins.lean:70`). -/
def LocalLawDetSeq (E t Ψ : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2)
    (fun n _ _ => Ψ n)

/-- The IBP display with a deterministic control (`Acta:4587`): `max_i |x_i - t m² Σ_k S_ik (G_kk -
m)| ≺ Ψ²`, `S = svar` the variance profile.  The left side is that of `hIBP` in the merged
`avg_bound_stochDom`.  RBM2D `IBPDet` (`Green/AvgPins.lean:78`). -/
def IBPDet (E t : ℕ → ℝ) (x : ∀ n, sz.SeqΩ → Vtx d (sz.L n) (sz.W n) → ℂ) (Ψ : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
    (fun n i ω => ‖x n ω i - (t n : ℂ) * mE (E n) ^ 2 *
      ∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
        (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
          mE (E n))‖)
    (fun n _ _ => Ψ n ^ 2)

/-- `jasdu` (`Acta:4571`) for the row family `t_k = S_ik`, deterministic control: the left side of
`hFArow` in the merged `avg_bound_stochDom`.  RBM2D `FARowDet` (`Green/AvgPins.lean:89`). -/
def FARowDet (E t : ℕ → ℝ) (x : ∀ n, sz.SeqΩ → Vtx d (sz.L n) (sz.W n) → ℂ) (Ψ : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n))
    (fun n i ω => ‖∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
      ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
        mE (E n)) - x n ω k)‖)
    (fun n _ _ => Ψ n ^ 2)

/-- `jasdu` (`Acta:4571`) for the block family `t_k = W^{-d} 1(k ∈ 𝓘_a)` (`E_a`), deterministic
control: the left side of `hFAblk` in the merged `avg_bound_stochDom`.  RBM2D `FABlkDet`
(`Green/AvgPins.lean:99`). -/
def FABlkDet (E t : ℕ → ℝ) (x : ∀ n, sz.SeqΩ → Vtx d (sz.L n) (sz.W n) → ℂ) (Ψ : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Zd d (sz.L n))
    (fun n a ω => ‖∑ k, (blkCoef2 d (sz.L n) (sz.W n) a k : ℂ) *
      ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
        mE (E n)) - x n ω k)‖)
    (fun n _ _ => Ψ n ^ 2)

/-- **The fixed-time fluctuation averaging, per-sequence form**: both families of `jasdu` at
`x = condDiagBlk`, control `Ψ²`.  RBM2D `FixedTimeFASeq` (`Green/AvgPins.lean:110`). -/
def FixedTimeFASeq (E t Ψ : ℕ → ℝ) : Prop :=
  FARowDet sz E t (condDiagBlk sz E t) Ψ ∧ FABlkDet sz E t (condDiagBlk sz E t) Ψ

/-- **The IBP display at `x = condDiagBlk`**.  RBM2D `IBPDetSeq` (`Green/AvgPins.lean:115`). -/
def IBPDetSeq (E t Ψ : ℕ → ℝ) : Prop :=
  IBPDet sz E t (condDiagBlk sz E t) Ψ

/-- `AsGMcSeq` is the local law at the scale `W^{-c}` (definitional).  RBM2D `asGMcSeq_iff`
(`Green/AvgPins.lean:119`). -/
theorem asGMcSeq_iff (E t : ℕ → ℝ) (c : ℝ) :
    AsGMcSeq sz E t c ↔ LocalLawDetSeq sz E t (fun n => ((sz.W n : ℕ) : ℝ) ^ (-c)) :=
  Iff.rfl

end Vocab

/-! ## 2. The pins

The floor of the control is the paper's `W^{-d/2} ≤ Ψ_t` (`3_5:27`; RBM2D `W⁻¹ ≤ Ψ` is this at
`d = 2`), written `((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n`; see the header. -/

section Pins

/-- **Pin LL** (RBM2D `Green/AvgPins.lean:134`, proved below by `localLawDetThm`): (`asGMc`)
(`3_5:30`) and `max 𝓛 ≺ Ψ²` with the floor `W^{-d/2} ≤ Ψ` give the local law `‖G - m‖_max ≺ Ψ`
(`Acta:4564`). -/
def LocalLawDetThm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t →
  ∀ c > (0 : ℝ), AsGMcSeq sz E t c →
  ∀ Ψ : ℕ → ℝ, (∀ n, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) → LoopDetSeq sz E t Ψ →
    LocalLawDetSeq sz E t Ψ

/-- **Pin FA** (RBM2D `FixedTimeFAThm`, `Green/AvgPins.lean:145`; paper `jasdu`, `Acta:4571`, the
fluctuation-averaging step of (`GavLGEX`), `3_5:33`).  Open: S1-30 (`fixedTimeFAThm`).  RBM1D's
`η ≥ N^{-K}` premise is derived from `RangeCond` (`eta_lower_of_rangeCond`). -/
def FixedTimeFAThm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
      Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq sz E t Ψ → FixedTimeFASeq sz E t Ψ

/-- **Pin IBP** (RBM2D `IBPDetThm`, `Green/AvgPins.lean:156`; the IBP display `Acta:4587`).  Same
premises as `FixedTimeFAThm`.  Open: S1-29, S1-30 (`ibpDetThm`). -/
def IBPDetThm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
      Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq sz E t Ψ → IBPDetSeq sz E t Ψ

/-- **Pin `AvgBoundDetThm`**: the merged `avg_bound_stochDom` with the controls `Ψ²` in place of
`maxLoopPM` and no `LoopDetSeq` step (RBM2D `Green/AvgPins.lean:167`); proved below
(`avgBoundDetThm`). -/
def AvgBoundDetThm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ 𝔠 𝔡 : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) →
  ∀ (x : ∀ n, sz.SeqΩ → Vtx d (sz.L n) (sz.W n) → ℂ) (Ψ : ℕ → ℝ),
    IBPDet sz E t x Ψ → FARowDet sz E t x Ψ → FABlkDet sz E t x Ψ → GavLDetSeq sz E t Ψ

/-- **Pin `LoopFloorThm`** (the floor; RBM2D `Green/AvgPins.lean:177`, `(W⁻¹)² ≤ 4 N^ε Ψ²`): under
(`asGMc`) and `max 𝓛 ≺ Ψ²`, for every `ε > 0`, eventually `W^{-d} ≤ 4 N^ε Ψ²`.  Paper: `Acta:4546`,
`c W⁻¹ ≤ max 𝓛` in `Ω(t,c)`, in `d` dimensions `W^{-d} ≤ 4 max 𝓛` (`inv_Wd_le_maxLoopPM`).
Proved below (`loopFloorThm`). -/
def LoopFloorThm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (𝔠 𝔡 : ℝ), 0 < 𝔠 → 0 < 𝔡 → sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| ≤ 2) → ∀ c > (0 : ℝ), AsGMcSeq sz E t c →
  ∀ Ψ : ℕ → ℝ, LoopDetSeq sz E t Ψ →
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ ε * Ψ n ^ 2

/-- **Pin `GavLDetFloorThm`** (RBM2D `Green/AvgPins.lean:187`): the (`GavLGEX`) clause of
`GbEXPHypV3` (`3_5:33`) for `Ψ ≥ W^{-d/2}` at every `n`.  Consumer: `gavLDetThm_of_floor`. -/
def GavLDetFloorThm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t →
  ∀ c > (0 : ℝ), AsGMcSeq sz E t c →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LoopDetSeq sz E t Ψ → GavLDetSeq sz E t Ψ

/-- **Pin `GavLDetThm`** (RBM2D `Green/AvgPins.lean:198`): the (`GavLGEX`) clause of `GbEXPHypV3`
(`3_5:33`), with its binders in the order of `GbEXPHypV3`.  Consumer:
`gbEXPV3Theorem_of_gavLDetThm`. -/
def GavLDetThm (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t →
  ∀ c > (0 : ℝ), AsGMcSeq sz E t c →
  ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LoopDetSeq sz E t Ψ → GavLDetSeq sz E t Ψ

end Pins

/-! ## 3. Private toolbox: the floor, cardinalities, bookkeeping -/

section Toolbox

/-- `(W^{-d/2})² = W^{-d}`. -/
private theorem localLaw_rpow_floor_sq (W d : ℕ) :
    (((W : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((W : ℕ) : ℝ) ^ d)⁻¹ := by
  have hW : (0 : ℝ) ≤ (W : ℝ) := Nat.cast_nonneg _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hW]
  have h : -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) := by push_cast; ring
  rw [h, Real.rpow_neg hW, Real.rpow_natCast]

private theorem localLaw_floor_nonneg {W d : ℕ} {Ψ : ℝ}
    (h : ((W : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) : 0 ≤ Ψ :=
  (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans h

private theorem localLaw_floor_sq_le {W d : ℕ} {Ψ : ℝ}
    (h : ((W : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) : (((W : ℕ) : ℝ) ^ d)⁻¹ ≤ Ψ ^ 2 := by
  rw [← localLaw_rpow_floor_sq W d]
  exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) h 2

/-- `W^{-d/2} ≤ W⁻¹` for `d ≥ 2` and `W ≥ 1`. -/
private theorem localLaw_floor_le_inv {W d : ℕ} (hW : 1 ≤ W) (hd : 2 ≤ d) :
    ((W : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ ((W : ℕ) : ℝ)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  calc ((W : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ ((W : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    _ = ((W : ℕ) : ℝ)⁻¹ := Real.rpow_neg_one _

variable {d : ℕ} (sz : Sizes d)

private theorem localLaw_card_Zd (L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

private theorem localLaw_Zd_le_size (n : ℕ) : (sz.L n) ^ d ≤ sz.size n := by
  rw [Sizes.size]
  exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

private theorem localLaw_card_vtx (n : ℕ) :
    Fintype.card (Vtx d (sz.L n) (sz.W n)) = sz.size n := by
  rw [Fintype.card_congr (splitEquiv d (sz.L n) (sz.W n)).symm, sz.card_Idx]

private theorem localLaw_card_Zd_le (n : ℕ) :
    Fintype.card (Zd d (sz.L n)) ≤ sz.size n ^ 1 := by
  rw [localLaw_card_Zd, pow_one]
  exact localLaw_Zd_le_size sz n

private theorem localLaw_card_Zd_sq_le (n : ℕ) :
    Fintype.card (Unit × Zd d (sz.L n) × Zd d (sz.L n)) ≤ sz.size n ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit, localLaw_card_Zd, one_mul, sq]
  exact Nat.mul_le_mul (localLaw_Zd_le_size sz n) (localLaw_Zd_le_size sz n)

private theorem localLaw_card_real_le {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (h : ∀ n, Fintype.card (V n) ≤ sz.size n ^ m) (n : ℕ) :
    (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (m : ℝ) := by
  rw [Real.rpow_natCast]; exact_mod_cast h n

/-- The grid union bound in the form used here: a per-time bound over an index set of size at most
`size^m` gives an event of high probability (RBM2D `highProb_of_perTime'`,
`Green/AvgPins.lean:356`). -/
private theorem localLaw_highProb_of_perTime {V : ℕ → Type*} [∀ n, Fintype (V n)] {m : ℕ}
    (hV : ∀ n, Fintype.card (V n) ≤ sz.size n ^ m)
    {ξ ζ : ∀ n, V n → sz.SeqΩ → ℝ} (h : sz.PrecPT ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt (seqP sz) sz.size
      (fun n => {ω | ∀ v, ξ n v ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n v ω}) :=
  RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt
    (stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := (m : ℝ)) (Nat.cast_nonneg m)
      (Eventually.of_forall (localLaw_card_real_le sz hV)) h) hτ

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually: the coupling window `Λ = 𝔡⁻¹` of `Kstab3`. -/
private theorem localLaw_lam_window {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  obtain ⟨_, _, _, _, hWO⟩ := hA
  filter_upwards [hWO] with n hn
  have hWpos : (0 : ℝ) < (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hn.1, hn.2⟩

private theorem localLaw_seqHflow_zero (n : ℕ) (ω : sz.SeqΩ) : sz.seqHflow n 0 ω = 0 := by
  rw [Sizes.seqHflow_eq_smul]
  simp

end Toolbox

/-! ## 4. The wiring (proved) -/

section Wiring

variable {d : ℕ}

/-- **The assembly.**  The four theorems of T2101 and the `GavLGEX` pin give `GbEXPV3Theorem`: the
premises of `GbEXPHypV3` are passed in their order.  RBM2D `gbEXPV3Theorem_of_gavLDetThm`
(`Green/AvgPins.lean:223`); `hd : 3 ≤ d` is that of `giiOmegaSeq`, `giiSeq_of_asGMc`. -/
theorem gbEXPV3Theorem_of_gavLDetThm (hd : 3 ≤ d) (h : GavLDetThm d) : GbEXPV3Theorem d := by
  intro sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR c hc
  exact ⟨gijOmegaSeq sz hκ hδ hA E t hE h0 h1 hR c hc,
    giiOmegaSeq sz hd hκ hδ hA E t hE h0 h1 hR c hc, fun hAs =>
      ⟨gijSeq_of_asGMc sz hκ hδ hA E t hE h0 h1 hR c hc hAs,
        giiSeq_of_asGMc sz hd hκ hδ hA E t hE h0 h1 hR c hc hAs,
        h sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR c hc hAs⟩⟩

/-- `LoopDetSeq` is monotone in the control.  RBM2D `loopDetSeq_mono`
(`Green/AvgPins.lean:232`). -/
theorem loopDetSeq_mono {sz : Sizes d} {E t Ψ Ψ' : ℕ → ℝ} (hΨ0 : ∀ n, 0 ≤ Ψ n)
    (hΨΨ' : ∀ n, Ψ n ≤ Ψ' n) (h : LoopDetSeq sz E t Ψ) : LoopDetSeq sz E t Ψ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn p
  refine le_trans (measure_mono fun ω hω => ?_) (hn p)
  have hsq : Ψ n ^ 2 ≤ Ψ' n ^ 2 := pow_le_pow_left₀ (hΨ0 n) (hΨΨ' n) 2
  have hN : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsq hN) hω

/-- **The safe-scale reduction** (RBM2D `gavLDetThm_of_floor`, `Green/AvgPins.lean:244`): the floor
lemma turns the statement for `Ψ ≥ W^{-d/2}` into the statement for every `Ψ ≥ 0`, at
`Ψ' = max(Ψ, W^{-d/2})` and `a' = min(a, 𝔠)`.  `2 ≤ d` is used only for `W^{-d/2} ≤ W⁻¹`. -/
theorem gavLDetThm_of_floor (hd : 2 ≤ d) (hL0 : LoopFloorThm d) (hF : GavLDetFloorThm d) :
    GavLDetThm d := by
  intro sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR c hc hAs Ψ a ha hΨ0 hΨhi hLoop
  have hbw := hA.2.2.2.1
  set Ψ' : ℕ → ℝ := fun n => max (Ψ n) (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) with hΨ'
  have hfl : ∀ n, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ' n := fun n => le_max_right _ _
  have hle : ∀ n, Ψ n ≤ Ψ' n := fun n => le_max_left _ _
  have hΨ'hi : ∀ᶠ n : ℕ in atTop, Ψ' n ≤ ((sz.size n : ℕ) : ℝ) ^ (-(min a 𝔠)) := by
    filter_upwards [hΨhi, hbw] with n hn hbwn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (-a) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(min a 𝔠)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (min_le_left _ _))
    have h2 : ((sz.W n : ℕ) : ℝ)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-𝔠) := by
      rw [Real.rpow_neg hN0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hbwn
    have h3 : ((sz.size n : ℕ) : ℝ) ^ (-𝔠) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(min a 𝔠)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (min_le_right _ _))
    exact max_le (hn.trans h1)
      ((localLaw_floor_le_inv (sz.W_pos n) hd).trans (h2.trans h3))
  have hG' := hF sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR c hc hAs Ψ' (min a 𝔠)
    (lt_min ha h𝔠) hfl hΨ'hi (loopDetSeq_mono hΨ0 hle hLoop)
  have hE2 : ∀ n, |E n| ≤ 2 := fun n => by linarith [hE n]
  have hfloor := hL0 sz 𝔠 𝔡 h𝔠 h𝔡 hA E t hE2 c hc hAs Ψ hLoop
  intro τ hτ D hD
  have h4 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < τ / 4)).comp hA.2.2.1).eventually_ge_atTop 4
  filter_upwards [hG' (τ / 2) (half_pos hτ) D hD, hfloor (τ / 4) (by positivity), h4] with
    n hn hfn h4n p
  refine le_trans (measure_mono fun ω hω => ?_) (hn p)
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hsq : Ψ' n ^ 2 ≤ 4 * N ^ (τ / 4) * Ψ n ^ 2 := by
    have hA' : Ψ n ^ 2 ≤ 4 * N ^ (τ / 4) * Ψ n ^ 2 := by
      have : (1 : ℝ) ≤ 4 * N ^ (τ / 4) := by linarith
      nlinarith [sq_nonneg (Ψ n)]
    rcases le_total (Ψ n) (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) with hc' | hc'
    · have : Ψ' n = ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := max_eq_right hc'
      rw [this, localLaw_rpow_floor_sq]
      exact hfn
    · have : Ψ' n = Ψ n := max_eq_left hc'
      rw [this]; exact hA'
  have hkey : N ^ (τ / 2) * Ψ' n ^ 2 ≤ N ^ τ * Ψ n ^ 2 := by
    have e1 : N ^ (τ / 2) * Ψ' n ^ 2 ≤ N ^ (τ / 2) * (4 * N ^ (τ / 4) * Ψ n ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0 _)
    have e2 : N ^ (τ / 2) * (4 * N ^ (τ / 4) * Ψ n ^ 2) ≤
        N ^ (τ / 2) * (N ^ (τ / 4) * N ^ (τ / 4) * Ψ n ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hN0 _)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right h4n (Real.rpow_nonneg hN0 _)
    have e3 : N ^ (τ / 2) * (N ^ (τ / 4) * N ^ (τ / 4) * Ψ n ^ 2) = N ^ τ * Ψ n ^ 2 := by
      rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add' hN0 (by positivity : τ / 2 + τ / 4 ≠ 0),
        ← Real.rpow_add' hN0 (by positivity : τ / 2 + τ / 4 + τ / 4 ≠ 0)]
      congr 2; ring
    linarith
  exact lt_of_le_of_lt hkey hω

/-- **The G4 chain**: LL, FA, IBP and the `≺ Ψ²`-input variant give the floor statement.  RBM2D
`gavLDetFloorThm_of_parts` (`Green/AvgPins.lean:300`). -/
theorem gavLDetFloorThm_of_parts (hLL : LocalLawDetThm d) (hFA : FixedTimeFAThm d)
    (hIBP : IBPDetThm d) (hAvg : AvgBoundDetThm d) : GavLDetFloorThm d := by
  intro sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR c hc hAs Ψ a ha hfl hΨhi hLoop
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => localLaw_floor_nonneg (hfl n)
  have hll := hLL sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR c hc hAs Ψ hfl hLoop
  have hev : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
      Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a) :=
    hΨhi.mono fun n hn => ⟨hfl n, hn⟩
  have hfa := hFA sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR Ψ a ha hΨ0 hev hll
  have hibp := hIBP sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR Ψ a ha hΨ0 hev hll
  exact hAvg sz κ 𝔠 𝔡 hκ h𝔠 h𝔡 hA E t (fun n => (hE n).le) h0 h1 (condDiagBlk sz E t) Ψ hibp
    hfa.1 hfa.2

/-- **The whole route**: the five pins give `GbEXPV3Theorem`.  RBM2D `gbEXPV3Theorem_of_parts`
(`Green/AvgPins.lean:314`). -/
theorem gbEXPV3Theorem_of_parts (hd : 3 ≤ d) (hLL : LocalLawDetThm d) (hFA : FixedTimeFAThm d)
    (hIBP : IBPDetThm d) (hAvg : AvgBoundDetThm d) (hL0 : LoopFloorThm d) : GbEXPV3Theorem d :=
  gbEXPV3Theorem_of_gavLDetThm hd
    (gavLDetThm_of_floor (by omega) hL0 (gavLDetFloorThm_of_parts hLL hFA hIBP hAvg))

end Wiring

/-! ## 5. `gexRHS ≤ 9^d max𝓛 + W^{-d}` and the `≺` calculus -/

section Gex

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem LocalLaw_zdist_le_one {y : ZMod L} (h : zdist L y ≤ 1) :
    y = 0 ∨ y = 1 ∨ y = -1 := by
  unfold zdist at h
  have hv : y.val < L := ZMod.val_lt y
  have hy : ((y.val : ℕ) : ZMod L) = y := ZMod.natCast_zmod_val y
  by_cases h1 : y.val ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h1'
    · left; rw [← hy, h0]; simp
    · right; left; rw [← hy, h1']; simp
  · right; right
    have h2 : L - y.val ≤ 1 := by omega
    have h3 : y.val = L - 1 := by omega
    rw [← hy, h3]
    have : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
    rw [Nat.cast_sub this]; simp

/-- **The near set has at most `3^d` points**: `{a' : |a' - a|_∞ ≤ 1}` (RBM2D `LocalLaw_near_card`,
`Green/LocalLaw.lean:91`: the `L¹` ball of `sbSupport`, 5 points; here the `L^∞` ball of the
merged `gexRHS`, `{0,1,-1}^d`, `3^d` points). -/
private theorem LocalLaw_near_card (a : Zd d L) :
    ((Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1).card : ℝ) ≤ (3 : ℝ) ^ d := by
  classical
  let T : Finset (ZMod L) := {0, 1, -1}
  have hT : T.card ≤ 3 := Finset.card_le_three
  have hsub : (Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1) ⊆
      (Fintype.piFinset fun _ : Fin d => T).image (fun f => f + a) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_image, Fintype.mem_piFinset]
    refine ⟨x - a, fun i => ?_, by simp⟩
    have h1 : zdist L ((x - a) i) ≤ 1 := by
      unfold zdistInf at hx
      exact le_trans (Finset.le_sup (f := fun j => zdist L ((x - a) j)) (Finset.mem_univ i)) hx
    rcases LocalLaw_zdist_le_one h1 with h | h | h <;> simp [T, h]
  have hc : (Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1).card ≤ 3 ^ d :=
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (Fintype.piFinset fun _ : Fin d => T).card := Finset.card_image_le
      _ = T.card ^ d := by simp [Fintype.card_piFinset]
      _ ≤ 3 ^ d := Nat.pow_le_pow_left hT d
  exact_mod_cast hc

private theorem LocalLaw_double_sum_ite {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop)
    (B : β → Prop) [DecidablePred A] [DecidablePred B] (m : ℝ) :
    ∑ a : α, ∑ b : β, (if A a ∧ B b then m else 0) =
      ((Finset.univ.filter A).card : ℝ) * (((Finset.univ.filter B).card : ℝ) * m) := by
  have h1 : ∀ a : α, ∑ b : β, (if A a ∧ B b then m else 0) =
      if A a then ((Finset.univ.filter B).card : ℝ) * m else 0 := by
    intro a
    by_cases ha : A a
    · simp only [ha, true_and, ite_true]
      rw [← Finset.sum_filter]; simp [Finset.sum_const, nsmul_eq_mul]
    · simp [ha]
  simp_rw [h1]
  rw [← Finset.sum_filter]; simp [Finset.sum_const, nsmul_eq_mul]

/-- The right side of (`GijGEX`) is at most `9^d B + W^{-d}` if every `|𝓛_{(+,-),(a,b)}| ≤ B` (the
number of `(a', b')` with `|a' - a|_∞, |b' - b|_∞ ≤ 1` is at most `3^d × 3^d`).  RBM2D
`LocalLaw_gexRHS_le` (`Green/LocalLaw.lean:104`), `5 × 5 = 25` there. -/
private theorem LocalLaw_gexRHS_le (E u B : ℝ) (hB : 0 ≤ B)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : ∀ a b, ‖loopPM d L W E u M a b‖ ≤ B)
    (a b : Zd d L) :
    gexRHS d L W E u M a b ≤ (9 : ℝ) ^ d * B + ((W : ℝ) ^ d)⁻¹ := by
  unfold gexRHS
  refine add_le_add ?_ ?_
  · calc (∑ a' : Zd d L, ∑ b' : Zd d L,
          if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
            ‖loopPM d L W E u M a' b'‖ else 0)
        ≤ ∑ a' : Zd d L, ∑ b' : Zd d L,
          if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then B else 0 := by
          refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
          split_ifs
          · exact hM a' b'
          · exact le_rfl
      _ = ((Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1).card : ℝ) *
          (((Finset.univ.filter fun x : Zd d L => zdistInf d L (x - b) ≤ 1).card : ℝ) * B) :=
          LocalLaw_double_sum_ite (fun x : Zd d L => zdistInf d L (x - a) ≤ 1)
            (fun x : Zd d L => zdistInf d L (x - b) ≤ 1) _
      _ ≤ (3 ^ d : ℝ) * ((3 ^ d : ℝ) * B) := by
          have h1 := LocalLaw_near_card a
          have h2 := LocalLaw_near_card b
          gcongr
      _ = (9 : ℝ) ^ d * B := by
          rw [← mul_assoc, ← mul_pow]; norm_num
  · split_ifs
    · exact le_rfl
    · positivity

/-- **The new lemma**: `gexRHS ≤ 9^d · maxLoopPM + W^{-d}`, pointwise (the double sum over the two
`L^∞` unit balls has at most `3^d × 3^d` terms, each `≤ maxLoopPM`; the diagonal-block term is
`≤ W^{-d}`).  RBM2D `LocalLaw_gexRHS_le_maxLoopPM` (`Green/LocalLaw.lean:139`), `25`, `W⁻²` there;
`hL : 3 ≤ L` is not used and is dropped. -/
theorem LocalLaw_gexRHS_le_maxLoopPM (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a b : Zd d L) :
    gexRHS d L W E u M a b ≤ (9 : ℝ) ^ d * maxLoopPM d L W E u M + ((W : ℝ) ^ d)⁻¹ :=
  LocalLaw_gexRHS_le E u _ (maxLoopPM_nonneg E u M) M
    (fun a b => Finset.le_sup' (fun p : Zd d L × Zd d L => ‖loopPM d L W E u M p.1 p.2‖)
      (Finset.mem_univ (a, b))) a b

/-- The fine entry `|(G - m)_{ij}|` for `i ≠ j` is `√(offSq)`.  RBM2D `LocalLaw_llErr_off`
(`Green/LocalLaw.lean:148`; no bridge `step2Local_llErrMat_eq` is needed: `offSq` is on `Idx`). -/
private theorem LocalLaw_llErr_off (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    {i j : Idx d L W} (hij : i ≠ j) :
    llErrMat d L W E u M i j = Real.sqrt (offSq d L W E u M i j) := by
  unfold llErrMat offSq
  simp only [hij, ite_false, sub_zero]
  rw [Real.sqrt_sq (norm_nonneg _)]

/-- The fine entry `|(G - m)_{ii}|` is `√(diagSq)`.  RBM2D `LocalLaw_llErr_diag`
(`Green/LocalLaw.lean:160`). -/
private theorem LocalLaw_llErr_diag (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (i : Idx d L W) :
    llErrMat d L W E u M i i = Real.sqrt (diagSq d L W E u M i) := by
  unfold llErrMat diagSq
  simp only [ite_true]
  rw [Real.sqrt_sq (norm_nonneg _)]

private theorem LocalLaw_offSq_nonneg (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (p q : Idx d L W) : 0 ≤ offSq d L W E u M p q := by
  unfold offSq
  split_ifs <;> positivity

private theorem LocalLaw_diagSq_nonneg (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (p : Idx d L W) : 0 ≤ diagSq d L W E u M p := by
  unfold diagSq
  positivity

end Gex

section Calc

/-- Reindexing a per-time domination along a map of index types `V l → U l`.  RBM2D
`LocalLaw_reindex` (`Green/LocalLaw.lean:184`). -/
private theorem LocalLaw_reindex {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U V : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ} (φ : ∀ l, V l → U l)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (U := V) (fun l v ω => ξ l (φ l v) ω) (fun l v ω => ζ l (φ l v) ω) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl v
  exact hl (φ l v)

/-- The real-number core of `LocalLaw_trans`: `a = s^{τ/4}`, `b = a² = s^{τ/2}`, `c = b² = s^τ`,
threshold `K + 1 ≤ b` (RBM2D `LocalLaw_absorb`, `Green/LocalLaw.lean:193`, `K = 25`, `26 ≤ b`). -/
private theorem LocalLaw_absorb {a b c X Y M Q K : ℝ} (hK : 0 ≤ K) (h1 : 1 ≤ a)
    (hKb : K + 1 ≤ b) (hab : a * a = b) (hbc : b * b = c) (hQ : 0 ≤ Q) (hX : X ≤ a * Y)
    (hM : M ≤ a * Q) (hY : Y ≤ K * M + Q) : X ≤ c * Q := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hab' : a ≤ b := by nlinarith
  have hY' : Y ≤ K * (a * Q) + Q := hY.trans (by linarith [mul_le_mul_of_nonneg_left hM hK])
  have e1 : X ≤ a * (K * (a * Q) + Q) := hX.trans (mul_le_mul_of_nonneg_left hY' ha0)
  have e2 : a * (K * (a * Q) + Q) = K * b * Q + a * Q := by rw [← hab]; ring
  have e3 : a * Q ≤ b * Q := mul_le_mul_of_nonneg_right hab' hQ
  have e4 : (K + 1) * b * Q ≤ b * b * Q :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKb hb0) hQ
  rw [← hbc]
  nlinarith

/-- **Transitivity with the constant `K + 1`**: if `X ≺ Y`, `M ≺ Q` and `Y ≤ K M + Q` pointwise
(`Q ≥ 0`, `K ≥ 0`), then `X ≺ Q`.  Proof by `perTimeCalc_of_imp_union` at `τ' = τ/4`:
`X ≤ N^{τ/4} Y ≤ N^{τ/4}(K N^{τ/4} Q + Q) ≤ (K+1) N^{τ/2} Q ≤ N^τ Q` once `N^{τ/2} ≥ K + 1`.  RBM2D
`LocalLaw_trans` (`Green/LocalLaw.lean:209`), `K = 25`. -/
private theorem LocalLaw_trans {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U : ℕ → Type*} (hsize : Tendsto size atTop atTop) {K : ℝ} (hK : 0 ≤ K)
    {X Y M : ∀ l, U l → Ω → ℝ} {Q : ℕ → ℝ}
    (hXY : PerTimeDomAt P size X Y) (hMQ : PerTimeDomAt P size M (fun l _ _ => Q l))
    (hQ : ∀ l, 0 ≤ Q l) (hY : ∀ l u ω, Y l u ω ≤ K * M l u ω + Q l) :
    PerTimeDomAt P size X (fun l _ _ => Q l) := by
  refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_of_imp_union hsize hXY hMQ ?_
  intro τ hτ
  refine ⟨τ / 4, by positivity, ?_⟩
  filter_upwards [hsize.eventually (eventually_le_rpow 1 (show 0 < τ / 4 by positivity)),
    hsize.eventually (eventually_le_rpow (K + 1) (show 0 < τ / 2 by positivity))]
    with l h1 hK1 u ω hlt
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨hX, hM⟩ := hcon
  have hs0 : (0 : ℝ) ≤ (size l : ℝ) := Nat.cast_nonneg _
  have hab : (size l : ℝ) ^ (τ / 4) * (size l : ℝ) ^ (τ / 4) = (size l : ℝ) ^ (τ / 2) := by
    rw [← Real.rpow_add' hs0 (by positivity : τ / 4 + τ / 4 ≠ 0)]; congr 1; ring
  have hbc : (size l : ℝ) ^ (τ / 2) * (size l : ℝ) ^ (τ / 2) = (size l : ℝ) ^ τ := by
    rw [← Real.rpow_add' hs0 (by positivity : τ / 2 + τ / 2 ≠ 0)]; congr 1; ring
  exact absurd hlt (not_lt.2 (LocalLaw_absorb hK h1 hK1 hab hbc (hQ l) hX hM (hY l u ω)))

end Calc

/-! ## 6. `max 𝓛 ≺ Ψ²` at a general index type, and `localLawDetThm` -/

section MaxLoop

variable {d : ℕ} (sz : Sizes d)

/-- `max_{a,b} |𝓛_{(+,-),(a,b)}| ≺ Ψ²` from `LoopDetSeq` (grid union over `(Z_L^d)²`,
`L^{2d} ≤ size²`, then `maxLoopPM = ‖loopPM a₀ b₀‖` for some pair), at any index type `V`.  RBM2D
`LocalLaw_maxLoop_dom` (`Green/LocalLaw.lean:253`). -/
private theorem LocalLaw_maxLoop_dom {E t : ℕ → ℝ} {Ψ : ℕ → ℝ} (hLoop : LoopDetSeq sz E t Ψ)
    (V : ℕ → Type*) :
    sz.PrecPT (U := V)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))
      (fun n _ _ => Ψ n ^ 2) := by
  have hS := stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := ((2 : ℕ) : ℝ))
    (Nat.cast_nonneg 2) (Eventually.of_forall (localLaw_card_real_le sz (localLaw_card_Zd_sq_le sz)))
    hLoop
  intro τ hτ D hD
  filter_upwards [hS τ hτ D hD] with n hn u
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  have hω' : ((sz.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 <
      maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) := hω
  unfold maxLoopPM at hω'
  obtain ⟨b, -, hb⟩ := (Finset.lt_sup'_iff _).1 hω'
  exact ⟨((), b.1, b.2), hb⟩

/-- **Pin LL proved: the local law at a deterministic control** (`LocalLawDetThm`).  Under
(`asGMc`) (`AsGMcSeq sz E t c`, `3_5:30`) and `LoopDetSeq sz E t Ψ` with the floor `W^{-d/2} ≤ Ψ`:
`max_{ij} |(G_t - m)_{ij}| ≺ Ψ` per time ([YY_25] proof of (`GavLGEX`), `Acta:4564`).  A
conditional statement (`AsGMcSeq`, `LoopDetSeq` are inputs); the hypotheses are exactly those of
the pin; `hd : 3 ≤ d` is that of `giiSeq_of_asGMc`.  RBM2D `localLawDetThm`
(`Green/LocalLaw.lean:279`). -/
theorem localLawDetThm (hd : 3 ≤ d) : LocalLawDetThm d := by
  intro sz κ 𝔠 𝔡 δ hκ h𝔠 h𝔡 hδ hA E t hE h0 h1 hR c hc hAs Ψ hΨ hLoop
  have hsz' := Sizes.tendsto_size sz hA.2.2.1
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => localLaw_floor_nonneg (hΨ n)
  have hΨ2 : ∀ n, 0 ≤ Ψ n ^ 2 := fun n => sq_nonneg _
  have hW2 : ∀ n, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Ψ n ^ 2 := fun n => localLaw_floor_sq_le (hΨ n)
  have hsq : ∀ n, Real.sqrt (Ψ n ^ 2) = Ψ n := fun n => Real.sqrt_sq (hΨ0 n)
  have hloop := LocalLaw_maxLoop_dom sz hLoop
  have h9 : (0 : ℝ) ≤ (9 : ℝ) ^ d := by positivity
  have h9' : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  -- off-diagonal: `offSq ≺ gexRHS ≤ 9^d maxLoopPM + W^{-d} ≤ 9^d maxLoopPM + Ψ²`, so `offSq ≺ Ψ²`
  have hoff : sz.PrecPT
      (U := fun n => Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2)
      (fun n _ _ => Ψ n ^ 2) :=
    LocalLaw_trans hsz' h9 (gijSeq_of_asGMc sz hκ hδ hA E t hE h0 h1 hR c hc hAs)
      (hloop (fun n => Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)))
      (Q := fun n => Ψ n ^ 2) hΨ2
      (fun n u ω => (LocalLaw_gexRHS_le_maxLoopPM _ _ _ _ _).trans
        (by have := hW2 n; linarith))
  -- diagonal: `diagSq ≺ maxLoopPM ≤ 9^d maxLoopPM + Ψ²`, so `diagSq ≺ Ψ²`
  have hdiag : sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n))
      (fun n p ω => diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2)
      (fun n _ _ => Ψ n ^ 2) :=
    LocalLaw_trans hsz' h9 (giiSeq_of_asGMc sz hd hκ hδ hA E t hE h0 h1 hR c hc hAs)
      (hloop (fun n => Unit × Idx d (sz.L n) (sz.W n)))
      (Q := fun n => Ψ n ^ 2) hΨ2
      (fun n u ω => by
        have h1' := maxLoopPM_nonneg (L := sz.L n) (W := sz.W n) (d := d) (E n) (t n)
          (sz.seqHflow n (t n) ω)
        have h2 := hΨ2 n
        change maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) ≤
          (9 : ℝ) ^ d * maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) +
            Ψ n ^ 2
        nlinarith)
  -- square roots: `√offSq ≺ Ψ`, `√diagSq ≺ Ψ`
  have hoffS : sz.PrecPT
      (U := fun n => Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => Real.sqrt
        (offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2))
      (fun n _ _ => Ψ n) := by
    have := RBM.Ind.PerTimeCalc.PerTime.sqrt_of
      (fun n p ω => LocalLaw_offSq_nonneg _ _ _ _ _) (fun n p ω => hΨ2 n) hoff
    simp only [hsq] at this
    exact this
  have hdiagS : sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n))
      (fun n p ω => Real.sqrt
        (diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2))
      (fun n _ _ => Ψ n) := by
    have := RBM.Ind.PerTimeCalc.PerTime.sqrt_of
      (fun n p ω => LocalLaw_diagSq_nonneg _ _ _ _) (fun n p ω => hΨ2 n) hdiag
    simp only [hsq] at this
    exact this
  -- back to the pair index, and the case split `i = j` / `i ≠ j`
  have h₂ := LocalLaw_reindex
    (fun n (p : Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      (((), p.2.1) : Unit × Idx d (sz.L n) (sz.W n))) hdiagS
  unfold LocalLawDetSeq
  refine RBM.Ind.PerTimeCalc.PerTime.stochDom_of_forall_or hsz' hoffS h₂ ?_
  intro n p ω
  obtain ⟨-, i, j⟩ := p
  by_cases hij : i = j
  · subst hij
    right
    exact ⟨(LocalLaw_llErr_diag _ _ _ _).le, le_rfl⟩
  · left
    exact ⟨(LocalLaw_llErr_off _ _ _ hij).le, le_rfl⟩

end MaxLoop

/-! ## 7. The two pins proved outright: `avgBoundDetThm` and `loopFloorThm` -/

section Proved

variable {d : ℕ}

/-- **Pin `AvgBoundDetThm` proved**.  The `hA` step of the merged `avg_bound_stochDom`
(`of_det` + `norm_avgErr_le`, constant `1 + 2 Kstab3 d 𝔡⁻¹ κ ≤ size^ε`, independent of `n`; RBM2D
`1 + 2 Kstab2 κ L_n`) with the deterministic control `Ψ²` in place of `maxLoopPM`; no good event, no
`LoopDetSeq`.  `hd : 3 ≤ d` is that of `norm_avgErr_le`.  RBM2D `avgBoundDetThm`
(`Green/AvgPins.lean:416`). -/
theorem avgBoundDetThm (hd : 3 ≤ d) : AvgBoundDetThm d := by
  intro sz κ 𝔠 𝔡 hκ h𝔠 h𝔡 hA E t hE ht0 ht1 x Ψ hIBP hFArow hFAblk
  have hsz' := Sizes.tendsto_size sz hA.2.2.1
  unfold GavLDetSeq Sizes.PrecPT
  refine of_det hsz' (fun n p ω => sq_nonneg (Ψ n))
    (Ξ := fun n Φ => {ω | (∀ i : Vtx d (sz.L n) (sz.W n),
        ‖x n ω i - (t n : ℂ) * mE (E n) ^ 2 *
          ∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
            (greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
              mE (E n))‖ ≤ Φ * Ψ n ^ 2) ∧
      (∀ i : Vtx d (sz.L n) (sz.W n),
        ‖∑ k, (svar d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) *
          ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
            mE (E n)) - x n ω k)‖ ≤ Φ * Ψ n ^ 2) ∧
      (∀ a : Zd d (sz.L n),
        ‖∑ k, (blkCoef2 d (sz.L n) (sz.W n) a k : ℂ) *
          ((greenBlk d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true k k -
            mE (E n)) - x n ω k)‖ ≤ Φ * Ψ n ^ 2)})
    ?_ (δ := fun _ => 0) (C := fun _ => 1 + 2 * Kstab3 d 𝔡⁻¹ κ)
    (fun _ => le_rfl) (c₀ := 1) one_pos
    (Eventually.of_forall fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun ε hε => hsz'.eventually (eventually_le_rpow _ hε)) 1 ?_
  · intro τ' hτ'
    have h1 := localLaw_highProb_of_perTime sz (m := 1) (fun n =>
      (le_of_eq (localLaw_card_vtx sz n)).trans (by rw [pow_one])) hIBP hτ'
    have h2 := localLaw_highProb_of_perTime sz (m := 1) (fun n =>
      (le_of_eq (localLaw_card_vtx sz n)).trans (by rw [pow_one])) hFArow hτ'
    have h3 := localLaw_highProb_of_perTime sz (m := 1) (localLaw_card_Zd_le sz) hFAblk hτ'
    exact RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono
      (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz'
        (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsz' h1 h2) h3)
      (Eventually.of_forall fun n ω hω => ⟨hω.1.1, hω.1.2, hω.2⟩)
  · filter_upwards [localLaw_lam_window sz hA] with n hlam ω Φ _ _ hmem
    rintro ⟨_, a⟩
    obtain ⟨hIBPω, hFArowω, hFAblkω⟩ := hmem
    have h := norm_avgErr_le hd (sz.three_le_L n) hlam.1 hlam.2 hκ (hE n) (ht0 n) (ht1 n)
      (sz.seqHflow n (t n) ω) (x n ω)
      (A := Φ * Ψ n ^ 2) (B := Φ * Ψ n ^ 2) (B' := Φ * Ψ n ^ 2)
      hIBPω hFArowω a (hFAblkω a)
    calc _ ≤ _ := h
      _ = _ := by ring

/-- **Pin `LoopFloorThm` proved**.  On `Ω(t, c/2)` (high probability by the merged
`entryDom_goodSet_highProb_of_asGMc`) the merged `entryDom_goodEvent_of_llErr` and
`inv_Wd_le_maxLoopPM` give `W^{-d} ≤ 4 max 𝓛`; `max 𝓛 ≺ Ψ²` then forbids `W^{-d} > 4 N^ε Ψ²`,
because both events would have probability `≤ N⁻¹` and cover the whole space.  No `hd`: the loop
floor needs no dimension.  RBM2D `loopFloorThm` (`Green/AvgPins.lean:462`). -/
theorem loopFloorThm (d : ℕ) : LoopFloorThm d := by
  intro sz 𝔠 𝔡 h𝔠 h𝔡 hA E t hE c hc hAs Ψ hLoop ε hε
  have hsz' := Sizes.tendsto_size sz hA.2.2.1
  have hbw := hA.2.2.2.1
  have hG := entryDom_goodSet_highProb_of_asGMc sz hA hc hAs
  have hM := LocalLaw_maxLoop_dom sz hLoop (fun _ => Unit)
  have hWhalf : ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(c / 2)) ≤ 1 / 2 := by
    filter_upwards [hbw, hsz'.eventually (eventually_le_rpow 2
      (show 0 < 𝔠 * (c / 2) by positivity))] with n hbwn h2
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWc : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (c / 2) := by
      calc (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (c / 2)) := h2
        _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (c / 2) := Real.rpow_mul hN0 _ _
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (c / 2) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hbwn (by positivity)
    rw [Real.rpow_neg hW.le]
    rw [inv_le_comm₀ (Real.rpow_pos_of_pos hW _) (by norm_num)]
    linarith
  filter_upwards [hG 1 one_pos, hM ε hε 1 one_pos, hWhalf,
    hsz'.eventually (eventually_ge_atTop 3)] with n hGn hMn hWn hN3
  by_contra hcon
  rw [not_le] at hcon
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN3' : (3 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN3
  have hsub : goodSet sz E t (c / 2) n ⊆
      {ω | N ^ ε * Ψ n ^ 2 <
        maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)} := by
    intro ω hω
    have hGE := entryDom_goodEvent_of_llErr d (sz.L n) (sz.W n) (E n) (t n) _
      (sz.seqHflow n (t n) ω) hω
    have hinv := inv_Wd_le_maxLoopPM (sz.seqHflow_isHermitian n (t n) ω) (hE n) hGE hWn
    change N ^ ε * Ψ n ^ 2 < _
    linarith
  have hbad := hMn ()
  have hP1 : seqP sz (goodSet sz E t (c / 2) n) ≤ ENNReal.ofReal (N ^ (-(1 : ℝ))) :=
    (measure_mono hsub).trans hbad
  have hsum : (1 : ENNReal) ≤ ENNReal.ofReal (2 * N ^ (-(1 : ℝ))) := by
    have hp : (0 : ℝ) ≤ N ^ (-(1 : ℝ)) := Real.rpow_nonneg (by linarith) _
    calc (1 : ENNReal) = seqP sz Set.univ := measure_univ.symm
      _ = seqP sz (goodSet sz E t (c / 2) n ∪ (goodSet sz E t (c / 2) n)ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ seqP sz (goodSet sz E t (c / 2) n) + seqP sz (goodSet sz E t (c / 2) n)ᶜ :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (N ^ (-(1 : ℝ))) + ENNReal.ofReal (N ^ (-(1 : ℝ))) :=
          add_le_add hP1 hGn
      _ = ENNReal.ofReal (2 * N ^ (-(1 : ℝ))) := by
          rw [← ENNReal.ofReal_add hp hp]; ring_nf
  have hlt : 2 * N ^ (-(1 : ℝ)) < 1 := by
    rw [Real.rpow_neg_one]
    have : N⁻¹ ≤ 1 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have := (ENNReal.ofReal_lt_one.2 hlt)
  exact absurd hsum (not_le.2 this)

/-- **The route with the two proved pins inserted**: only the three pins LL, FA, IBP remain.  RBM2D
`gbEXPV3Theorem_of_ports` (`Green/AvgPins.lean:518`). -/
theorem gbEXPV3Theorem_of_ports (hd : 3 ≤ d) (hLL : LocalLawDetThm d) (hFA : FixedTimeFAThm d)
    (hIBP : IBPDetThm d) : GbEXPV3Theorem d :=
  gbEXPV3Theorem_of_parts hd hLL hFA hIBP (avgBoundDetThm hd) (loopFloorThm d)

/-- **The route with LL, `AvgBoundDetThm` and the floor proved**: only the pins FA and IBP remain
(S1-28, S1-29, S1-30).  New (RBM2D's `LocalLaw.lean` is a separate file after `AvgPins`). -/
theorem LocalLaw_gbEXPV3Theorem_of_fa_ibp (hd : 3 ≤ d) (hFA : FixedTimeFAThm d) (hIBP : IBPDetThm d) :
    GbEXPV3Theorem d :=
  gbEXPV3Theorem_of_ports hd (localLawDetThm hd) hFA hIBP

end Proved

/-! ## 8. Extreme inputs: `t ≡ 0`, `W ≡ 1`, `t → 1` -/

section Extreme

variable {d : ℕ} (sz : Sizes d)

/-- **`t ≡ 0`, pin LL's conclusion**: `LocalLawDetSeq` holds at `t ≡ 0` for every `Ψ ≥ 0` (at
`H = 0`, `G = m 1`).  RBM2D `localLawDetSeq_time_zero` (`Green/AvgPins.lean:553`). -/
theorem localLawDetSeq_time_zero {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2) {Ψ : ℕ → ℝ}
    (hΨ : ∀ n, 0 ≤ Ψ n) : LocalLawDetSeq sz E (fun _ => 0) Ψ :=
  perTimeDomAt_of_nonpos _ _ _ _
    (fun n p ω => by
      simp only [localLaw_seqHflow_zero, llErrMat_time_zero (hE n), le_refl])
    (fun n _ _ => hΨ n)

/-- At `t ≡ 0`, `E_k(G_kk - m) = 0`.  RBM2D `condDiagBlk_time_zero` (`Green/AvgPins.lean:560`). -/
theorem condDiagBlk_time_zero {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2) (n : ℕ) (ω : sz.SeqΩ)
    (k : Vtx d (sz.L n) (sz.W n)) : condDiagBlk sz E (fun _ => 0) n ω k = 0 := by
  unfold condDiagBlk
  simp only [localLaw_seqHflow_zero, greenBlk_time_zero (hE n), Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self, condRow_const]

/-- **`t ≡ 0`, pin FA's conclusion**: `FixedTimeFASeq` holds at `t ≡ 0` for every `Ψ`.  RBM2D
`fixedTimeFASeq_time_zero` (`Green/AvgPins.lean:567`). -/
theorem fixedTimeFASeq_time_zero {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2) (Ψ : ℕ → ℝ) :
    FixedTimeFASeq sz E (fun _ => 0) Ψ := by
  constructor
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n i ω => ?_) (fun n _ _ => sq_nonneg _)
    simp only [localLaw_seqHflow_zero, greenBlk_time_zero (hE n), condDiagBlk_time_zero sz hE,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self, mul_zero,
      Finset.sum_const_zero, norm_zero, le_refl]
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n i ω => ?_) (fun n _ _ => sq_nonneg _)
    simp only [localLaw_seqHflow_zero, greenBlk_time_zero (hE n), condDiagBlk_time_zero sz hE,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self, mul_zero,
      Finset.sum_const_zero, norm_zero, le_refl]

/-- **`t ≡ 0`, pin IBP's conclusion**: `IBPDetSeq` holds at `t ≡ 0` for every `Ψ`.  RBM2D
`ibpDetSeq_time_zero` (`Green/AvgPins.lean:580`). -/
theorem ibpDetSeq_time_zero {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2) (Ψ : ℕ → ℝ) :
    IBPDetSeq sz E (fun _ => 0) Ψ := by
  refine perTimeDomAt_of_nonpos _ _ _ _ (fun n i ω => ?_) (fun n _ _ => sq_nonneg _)
  simp only [localLaw_seqHflow_zero, greenBlk_time_zero (hE n), condDiagBlk_time_zero sz hE,
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self, mul_zero,
    Complex.ofReal_zero, zero_mul, norm_zero, le_refl]

/-- **`W ≡ 1`**: `SizeTendsto` and `Bandwidth 𝔠` (`𝔠 > 0`) cannot hold together, so every pin above
is vacuous (not false) at `W ≡ 1`.  RBM2D `not_sizeTendsto_bandwidth_of_W_one`
(`Green/AvgPins.lean:589`). -/
theorem not_sizeTendsto_bandwidth_of_W_one (hW : ∀ n, sz.W n = 1) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) :
    ¬ (sz.SizeTendsto ∧ sz.Bandwidth 𝔠) := by
  rintro ⟨hsz, hbw⟩
  have h2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 𝔠 :=
    ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop 2
  obtain ⟨n, hn1, hn2⟩ := (hbw.and h2).exists
  rw [hW n] at hn1
  norm_num at hn1
  linarith

/-- **`t → 1`** (the `RangeCond` edge): RBM1D's premise `η_t ≥ N^{-K}` of FA/IBP holds with
`K = 1`, derived: `Im z = (1 - t) Im m ≥ N^{-1+δ} √(κ(4-κ))/2 ≥ N^{-1}` eventually.  RBM2D
`eta_lower_of_rangeCond` (`Green/AvgPins.lean:601`). -/
theorem eta_lower_of_rangeCond {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hsz : sz.SizeTendsto)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| < 2 - κ) (hR : sz.RangeCond δ t) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ (zt (E n) (t n)).im := by
  have hκ2 : κ < 2 := by linarith [abs_nonneg (E 0), hE 0]
  set c0 : ℝ := Real.sqrt (κ * (4 - κ)) / 2 with hc0
  have hc0pos : 0 < c0 := by
    rw [hc0]; exact div_pos (Real.sqrt_pos.2 (by nlinarith)) (by norm_num)
  have hlarge : ∀ᶠ n : ℕ in atTop, c0⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ δ :=
    ((tendsto_rpow_atTop hδ).comp hsz).eventually_ge_atTop c0⁻¹
  filter_upwards [hR, hlarge] with n hRn hln
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hm : c0 ≤ (mE (E n)).im := by
    rw [mE_im, hc0]
    have hE2 : E n ^ 2 ≤ (2 - κ) ^ 2 := by
      have h := hE n
      have : |E n| ^ 2 ≤ (2 - κ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h.le 2
      rwa [sq_abs] at this
    have : κ * (4 - κ) ≤ 4 - E n ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt this) (by norm_num)
  have hsplit : N ^ (-1 + δ) = N ^ (-1 : ℝ) * N ^ δ := Real.rpow_add hN0 _ _
  have hp : 0 ≤ N ^ (-1 : ℝ) := Real.rpow_nonneg hN0.le _
  have h1t : N ^ (-1 : ℝ) * N ^ δ ≤ 1 - t n := hsplit ▸ hRn
  have hkey : N ^ (-1 : ℝ) ≤ N ^ (-1 : ℝ) * N ^ δ * c0 := by
    have : 1 ≤ N ^ δ * c0 := by
      have h := mul_le_mul_of_nonneg_right hln hc0pos.le
      rwa [inv_mul_cancel₀ hc0pos.ne'] at h
    nlinarith
  rw [zt_im]
  calc N ^ (-1 : ℝ) ≤ N ^ (-1 : ℝ) * N ^ δ * c0 := hkey
    _ ≤ (1 - t n) * (mE (E n)).im :=
        mul_le_mul h1t hm hc0pos.le (le_trans (by positivity) h1t)

end Extreme

/-! ## 9. Compiled nonempty instances at `d = 3`

The data are those of `Green/Pins.lean` section 9 (`Instance.premises`): the merged preflight
sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`;
`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; the energy
`E_n = lemE z_n` with `z_n = 1/2 + i N_n^{-4/5}`, `κ = δ = (1/10)/2`, and the time sequence
`t ≡ 1/16` (every deterministic hypothesis of the pins is `Instance.premises`); the control is
`Ψ_n = W_n⁻¹`, which satisfies the floor `W_n^{-3/2} ≤ Ψ_n` (`W_n ≥ 32`) and `Ψ_n ≤ N_n^{-1/6}`
(`Bandwidth`).  What stays a hypothesis of an example at `t ≡ 1/16` is another gate's input: the
random premises `AsGMcSeq` (`ε₀ = 1/40`), `LoopDetSeq` (`(initialGT2)`, `3_5:30`), the outputs of
the pins FA and IBP (S1-28, S1-29, S1-30).  At `t ≡ 0` (`H = 0`, `G = m 1`) every hypothesis of
`localLawDetThm`, `loopFloorThm`, `avgBoundDetThm` is proved, with `Ψ_n = W_n^{-3/2}`
(`LoopDetSeq` by the exact value `‖𝓛_{(+,-),(a,b)}‖ ≤ W^{-d}`). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Green.Instance

private theorem localLaw_inst_hE (n : ℕ) : |STflowE z0 n| ≤ 2 :=
  (abs_lemE_lt_two (z0_im_pos n)).le

/-- `Ψ_n = W_n⁻¹ ≤ N_n^{-1/6}` (`Bandwidth` of `sz0` at `𝔠 = 1/6`). -/
private theorem localLaw_inst_W_inv_le (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ)⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 6 : ℝ)) := by
  have hN0 : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ) := by
    have := sz0.one_le_size n
    exact_mod_cast (by omega : 0 < sz0.size n)
  rw [Real.rpow_neg hN0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) (sz0_bandwidth_at n)

/-- `W_n⁻¹` satisfies the floor `W_n^{-3/2} ≤ Ψ_n` at `d = 3`. -/
private theorem localLaw_inst_floor (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ ((sz0.W n : ℕ) : ℝ)⁻¹ :=
  localLaw_floor_le_inv (sz0.W_pos n) (by norm_num)

/-- `RangeCond δ` at `t ≡ 0` for `δ ≤ 1`: `N^{-1+δ} ≤ 1 = 1 - 0`. -/
private theorem localLaw_inst_rangeCond_zero {δ : ℝ} (hδ : δ ≤ 1) :
    sz0.RangeCond δ (fun _ => 0) :=
  Eventually.of_forall fun n => by
    have hN1 : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast sz0.one_le_size n
    simpa using Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith : -1 + δ ≤ 0)

/-- At `t = 0`, `M = 0`: `‖𝓛_{(+,-),(a,b)}‖ ≤ W^{-d}` (`G = m 1`, `|m| = 1`).  RBM2D
`chk_norm_loopPM_zero` (`Green/EntryDom.lean:940`), for every bulk energy. -/
private theorem localLaw_norm_loopPM_zero {E : ℝ} (hE : |E| ≤ 2) (d L W : ℕ) [NeZero L]
    [NeZero W] (a b : Zd d L) :
    ‖loopPM d L W E 0 (0 : Matrix (Idx d L W) (Idx d L W) ℂ) a b‖ ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [norm_loopPM_eq _ Matrix.isHermitian_zero, greenBlk_time_zero hE]
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hm : ‖mE E‖ = 1 := norm_mE hE
  have h1 : ∀ β : Fin (W ^ d), ∑ α : Fin (W ^ d),
      ‖(mE E • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) (b, β) (a, α)‖ ^ 2 ≤ 1 := by
    intro β
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single β]
      · simp [hm]
      · intro α _ hne
        have h0 : (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a, β) (a, α) = 0 :=
          Matrix.one_apply_ne (fun h => hne (Prod.mk.inj h).2.symm)
        simp [h0]
      · simp
    · simp [Prod.ext_iff, hab, eq_comm]
  calc (((W : ℝ)⁻¹ ^ d) ^ 2) * ∑ β : Fin (W ^ d), ∑ α : Fin (W ^ d),
        ‖(mE E • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) (b, β) (a, α)‖ ^ 2
      ≤ (((W : ℝ)⁻¹ ^ d) ^ 2) * ∑ _β : Fin (W ^ d), (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β _ => h1 β) (by positivity)
    _ = ((W : ℝ) ^ d)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow]
        push_cast
        field_simp [pow_pos hW d |>.ne']

/-- `LoopDetSeq` at `t ≡ 0` with the floor itself as control, `Ψ_n = W_n^{-3/2}`
(`Ψ_n² = W_n^{-3}`), along the energy `lemE z_n`. -/
private theorem localLaw_inst_loopDet_zero :
    LoopDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) := by
  refine Sizes.precPT_of_le sz0 (fun n u ω => sq_nonneg _) (fun n u ω => ?_)
  simp only [localLaw_seqHflow_zero]
  rw [localLaw_rpow_floor_sq]
  exact localLaw_norm_loopPM_zero (localLaw_inst_hE n) 3 _ _ _ _

/-- **`localLawDetThm` at `t ≡ 1/16`**: every deterministic hypothesis is discharged
(`Admissible`, bulk, `0 ≤ t < 1`, `RangeCond`, `c = 1/40 > 0`, the floor); `AsGMcSeq` and
`LoopDetSeq` stay hypotheses. -/
example (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
    (hLoop : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) :
    LocalLawDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  localLawDetThm (d := 3) (by norm_num) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) premises.1 (STflowE z0) tInst
    premises.2.1 premises.2.2.1 premises.2.2.2.1 premises.2.2.2.2 (1 / 40) (by norm_num) hAs _
    localLaw_inst_floor hLoop

/-- **`localLawDetThm` at `t ≡ 0`, no hypothesis left**: `AsGMcSeq` by `asGMcSeq_time_zero`,
`LoopDetSeq` by the exact loop value, the floor with equality `Ψ_n = W_n^{-3/2}`. -/
example : LocalLawDetSeq sz0 (STflowE z0) (fun _ => 0)
    (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) :=
  localLawDetThm (d := 3) (by norm_num) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) premises.1 (STflowE z0) (fun _ => 0)
    premises.2.1 (fun _ => le_rfl) (fun _ => one_pos)
    (localLaw_inst_rangeCond_zero (by norm_num)) (1 / 40) (by norm_num)
    (asGMcSeq_time_zero sz0 localLaw_inst_hE _) _ (fun _ => le_rfl) localLaw_inst_loopDet_zero

/-- **`loopFloorThm` at `t ≡ 1/16`**: `AsGMcSeq`, `LoopDetSeq` stay hypotheses. -/
example (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
    (hLoop : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤
      4 * ((sz0.size n : ℕ) : ℝ) ^ ε * (((sz0.W n : ℕ) : ℝ)⁻¹) ^ 2 :=
  loopFloorThm 3 sz0 (1 / 6) (1 / 10) (by norm_num) (by norm_num) premises.1 (STflowE z0) tInst
    localLaw_inst_hE (1 / 40) (by norm_num) hAs _ hLoop ε hε

/-- **`loopFloorThm` at `t ≡ 0`, no hypothesis left**. -/
example (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤
      4 * ((sz0.size n : ℕ) : ℝ) ^ ε *
        (((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) ^ 2 :=
  loopFloorThm 3 sz0 (1 / 6) (1 / 10) (by norm_num) (by norm_num) premises.1 (STflowE z0)
    (fun _ => 0) localLaw_inst_hE (1 / 40) (by norm_num)
    (asGMcSeq_time_zero sz0 localLaw_inst_hE _) _ localLaw_inst_loopDet_zero ε hε

/-- **`avgBoundDetThm` at `t ≡ 1/16`**: the three inputs `IBPDet`, `FARowDet`, `FABlkDet` at
`x = condDiagBlk` are the outputs of the pins FA, IBP and stay hypotheses; everything else is
discharged. -/
example (hIBP : IBPDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹))
    (hFA : FixedTimeFASeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) :
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  avgBoundDetThm (d := 3) (by norm_num) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) (by norm_num)
    (by norm_num) (by norm_num) premises.1 (STflowE z0) tInst (fun n => (premises.2.1 n).le)
    premises.2.2.1 premises.2.2.2.1 (condDiagBlk sz0 (STflowE z0) tInst) _ hIBP hFA.1 hFA.2

/-- **`avgBoundDetThm` at `t ≡ 0`, no hypothesis left**: `IBPDet`, `FARowDet`, `FABlkDet` at
`x = condDiagBlk` hold by `ibpDetSeq_time_zero`, `fixedTimeFASeq_time_zero`. -/
example : GavLDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  avgBoundDetThm (d := 3) (by norm_num) sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) (by norm_num)
    (by norm_num) (by norm_num) premises.1 (STflowE z0) (fun _ => 0)
    (fun n => (premises.2.1 n).le) (fun _ => le_rfl) (fun _ => one_pos)
    (condDiagBlk sz0 (STflowE z0) (fun _ => 0)) _
    (ibpDetSeq_time_zero sz0 localLaw_inst_hE _)
    (fixedTimeFASeq_time_zero sz0 localLaw_inst_hE _).1
    (fixedTimeFASeq_time_zero sz0 localLaw_inst_hE _).2

/-- **`GbEXPHypV3` at the instance, from the pins**: the third clause (`(GavLGEX)`) with the pin
`GbEXPV3Theorem 3` obtained from the five pins; the stochastic inputs stay hypotheses. -/
private theorem localLaw_inst_gavL (h : GbEXPV3Theorem 3)
    (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
    (hLoop : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) :
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  ((inst_hyp h) premises.1 (STflowE z0) tInst premises.2.1 premises.2.2.1 premises.2.2.2.1
    premises.2.2.2.2 (1 / 40) (by norm_num)).2.2 hAs |>.2.2 _ (1 / 6) (by norm_num)
    (fun n => by positivity) (Eventually.of_forall localLaw_inst_W_inv_le) hLoop

/-- **`gbEXPV3Theorem_of_gavLDetThm`, instantiated** at `d = 3`, `sz0`, `t ≡ 1/16`. -/
example (hG : GavLDetThm 3) (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
    (hLoop : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) :
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  localLaw_inst_gavL (gbEXPV3Theorem_of_gavLDetThm (by norm_num) hG) hAs hLoop

/-- **`gavLDetThm_of_floor`, instantiated** at `d = 3`, `sz0`, `t ≡ 1/16`, `Ψ = W⁻¹`: the floor
lemma `loopFloorThm 3` is proved; `GavLDetFloorThm 3` (the chain FA, IBP) is the pin that stays a
hypothesis. -/
example (hF : GavLDetFloorThm 3) (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
    (hLoop : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) :
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  gavLDetThm_of_floor (by norm_num) (loopFloorThm 3) hF sz0 ((1 / 10) / 2) (1 / 6) (1 / 10)
    ((1 / 10) / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) premises.1
    (STflowE z0) tInst premises.2.1 premises.2.2.1 premises.2.2.2.1 premises.2.2.2.2 (1 / 40)
    (by norm_num) hAs _ (1 / 6) (by norm_num) (fun n => by positivity)
    (Eventually.of_forall localLaw_inst_W_inv_le) hLoop

/-- **`gavLDetFloorThm_of_parts`, instantiated** at `d = 3`, `sz0`, `t ≡ 1/16`, `Ψ = W⁻¹`:
`localLawDetThm` and `avgBoundDetThm` are proved; the pins FA and IBP stay hypotheses. -/
example (hFA : FixedTimeFAThm 3) (hIBP : IBPDetThm 3)
    (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
    (hLoop : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) :
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  gavLDetFloorThm_of_parts (localLawDetThm (by norm_num)) hFA hIBP (avgBoundDetThm (by norm_num))
    sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) premises.1 (STflowE z0) tInst premises.2.1 premises.2.2.1 premises.2.2.2.1
    premises.2.2.2.2 (1 / 40) (by norm_num) hAs _ (1 / 6) (by norm_num) localLaw_inst_floor
    (Eventually.of_forall localLaw_inst_W_inv_le) hLoop

/-- **`gbEXPV3Theorem_of_parts`, `_of_ports`, `LocalLaw_gbEXPV3Theorem_of_fa_ibp`, instantiated** at `d = 3`, `sz0`,
`t ≡ 1/16`, `Ψ = W⁻¹`: the pins FA, IBP stay hypotheses; `AsGMcSeq`, `LoopDetSeq` stay
hypotheses. -/
example (hFA : FixedTimeFAThm 3) (hIBP : IBPDetThm 3)
    (hAs : AsGMcSeq sz0 (STflowE z0) tInst (1 / 40))
    (hLoop : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹)) :
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) ∧
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) ∧
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  ⟨localLaw_inst_gavL (gbEXPV3Theorem_of_parts (by norm_num) (localLawDetThm (by norm_num)) hFA
      hIBP (avgBoundDetThm (by norm_num)) (loopFloorThm 3)) hAs hLoop,
    localLaw_inst_gavL (gbEXPV3Theorem_of_ports (by norm_num) (localLawDetThm (by norm_num)) hFA
      hIBP) hAs hLoop,
    localLaw_inst_gavL (LocalLaw_gbEXPV3Theorem_of_fa_ibp (by norm_num) hFA hIBP) hAs hLoop⟩

/-- **`loopDetSeq_mono`, instantiated** at `t ≡ 0`: `Ψ_n = W_n^{-3/2} ≤ Ψ'_n = W_n⁻¹`. -/
example : LoopDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) :=
  loopDetSeq_mono (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) localLaw_inst_floor
    localLaw_inst_loopDet_zero

/-- **`asGMcSeq_iff`, instantiated** at `t ≡ 0`, `c = 1/40`. -/
example : LocalLawDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 40 : ℝ))) :=
  (asGMcSeq_iff sz0 (STflowE z0) (fun _ => 0) (1 / 40)).1
    (asGMcSeq_time_zero sz0 localLaw_inst_hE _)

/-- **`localLawDetSeq_time_zero`, `fixedTimeFASeq_time_zero`, `ibpDetSeq_time_zero`,
`condDiagBlk_time_zero`, instantiated** along `lemE z_n`. -/
example : LocalLawDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) ∧
    FixedTimeFASeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) ∧
    IBPDetSeq sz0 (STflowE z0) (fun _ => 0) (fun n => ((sz0.W n : ℕ) : ℝ)⁻¹) ∧
    (∀ (ω : sz0.SeqΩ) (k : Vtx 3 (sz0.L 0) (sz0.W 0)),
      condDiagBlk sz0 (STflowE z0) (fun _ => 0) 0 ω k = 0) :=
  ⟨localLawDetSeq_time_zero sz0 localLaw_inst_hE (fun n => by positivity),
    fixedTimeFASeq_time_zero sz0 localLaw_inst_hE _, ibpDetSeq_time_zero sz0 localLaw_inst_hE _,
    fun ω k => condDiagBlk_time_zero sz0 localLaw_inst_hE 0 ω k⟩

/-- **`eta_lower_of_rangeCond`, instantiated**: `κ = δ = (1/10)/2`, `t ≡ 1/16`, along `lemE z_n`;
no hypothesis left. -/
example : ∀ᶠ n : ℕ in atTop, ((sz0.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤
    (zt (STflowE z0 n) (tInst n)).im :=
  eta_lower_of_rangeCond sz0 (κ := (1 / 10) / 2) (δ := (1 / 10) / 2) (by norm_num) (by norm_num)
    sz0_tendsto premises.2.1 premises.2.2.2.2

/-- **`not_sizeTendsto_bandwidth_of_W_one`, instantiated**: the size sequence `L_n = n + 3`,
`W_n ≡ 1`, `d = 3` (`N_n = (n+3)^3 → ∞`, but `W = 1 < N^{1/6}` eventually). -/
example :
    ¬ ((⟨fun n => n + 3, fun _ => 1, fun _ => 1, fun n => by omega, fun _ => one_pos⟩ :
        Sizes 3).SizeTendsto ∧
      (⟨fun n => n + 3, fun _ => 1, fun _ => 1, fun n => by omega, fun _ => one_pos⟩ :
        Sizes 3).Bandwidth (1 / 6)) :=
  not_sizeTendsto_bandwidth_of_W_one
    (⟨fun n => n + 3, fun _ => 1, fun _ => 1, fun n => by omega, fun _ => one_pos⟩ : Sizes 3)
    (fun _ => rfl) (by norm_num)

/-- **`LocalLaw_gexRHS_le_maxLoopPM`, instantiated** at the model matrix of `sz0` (`d = 3`,
`L = 4`, `W = 32`), every `E`, `u`, `ω`, `a`, `b`. -/
example (E u : ℝ) (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :
    gexRHS 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) a b ≤
      (9 : ℝ) ^ 3 * maxLoopPM 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) +
        (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ :=
  LocalLaw_gexRHS_le_maxLoopPM E u _ a b

/-- The same at `d = 3`, `L = 3`, `W = 1`, `E = 0`, `u = 1/2`, `M = 0`, `a = b = 0`. -/
example : gexRHS 3 3 1 0 (1 / 2) 0 0 0 ≤
    (9 : ℝ) ^ 3 * maxLoopPM 3 3 1 0 (1 / 2) 0 + (((1 : ℕ) : ℝ) ^ 3)⁻¹ :=
  LocalLaw_gexRHS_le_maxLoopPM (d := 3) (L := 3) (W := 1) 0 (1 / 2) 0 0 0

/-- **The literal port of RBM2D's `LoopFloorThm` is false at `d = 3`** (RBM2D
`Green/AvgPins.lean:177`: `(W⁻¹)² ≤ 4 N^ε Ψ²`, the floor `W⁻¹` of `d = 2`): at `sz0`, `E_n = lemE z_n`,
`t ≡ 0` every hypothesis holds (`Admissible`, `AsGMcSeq` at every `c` by `asGMcSeq_time_zero`,
`LoopDetSeq` at `Ψ_n = W_n^{-3/2}` by the exact loop value `W^{-d}`), and the conclusion fails at
`ε = 1/18`: it reads `W_n ≤ 4 N_n^{1/18}` with `W_n = 32 (n+1)^5`, `N_n = 2^{21} (n+1)^{18}`.  So
the floor of `LoopFloorThm d` is `W^{-d}` (`3_5:27`), not `(W⁻¹)²`; paper-delta candidate `T2108a`. -/
theorem LocalLaw_loopFloor_literal_false :
    ¬ ∀ (sz : Sizes 3) (𝔠 𝔡 : ℝ), 0 < 𝔠 → 0 < 𝔡 → sz.Admissible 𝔠 𝔡 →
      ∀ E t : ℕ → ℝ, (∀ n, |E n| ≤ 2) → ∀ c > (0 : ℝ), AsGMcSeq sz E t c →
      ∀ Ψ : ℕ → ℝ, LoopDetSeq sz E t Ψ →
      ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        (((sz.W n : ℕ) : ℝ)⁻¹) ^ 2 ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ ε * Ψ n ^ 2 := by
  intro h
  have hev := h sz0 (1 / 6) (1 / 10) (by norm_num) (by norm_num) sz0_admissible (STflowE z0)
    (fun _ => 0) localLaw_inst_hE (1 / 40) (by norm_num)
    (asGMcSeq_time_zero sz0 localLaw_inst_hE _) _ localLaw_inst_loopDet_zero (1 / 18)
    (by norm_num)
  obtain ⟨n, hn, hn1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hm : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  set m : ℝ := (n : ℝ) + 1 with hmdef
  have hm0 : 0 < m := by linarith
  have hW : ((sz0.W n : ℕ) : ℝ) = 32 * m ^ 5 := by
    simp only [sz0, hmdef]; push_cast; ring
  have hN : ((sz0.size n : ℕ) : ℝ) = 2097152 * m ^ 18 := by
    simp only [Sizes.size, sz0, hmdef]; push_cast; ring
  have hNle : ((sz0.size n : ℕ) : ℝ) ≤ (3 * m) ^ 18 := by
    rw [hN, mul_pow]
    have : (0 : ℝ) ≤ m ^ 18 := by positivity
    nlinarith
  have hX : ((sz0.size n : ℕ) : ℝ) ^ (1 / 18 : ℝ) ≤ 3 * m := by
    calc ((sz0.size n : ℕ) : ℝ) ^ (1 / 18 : ℝ) ≤ ((3 * m) ^ 18) ^ (1 / 18 : ℝ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hNle (by norm_num)
      _ = 3 * m := by
          rw [show (1 / 18 : ℝ) = ((18 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  have hw : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by rw [hW]; positivity
  rw [localLaw_rpow_floor_sq] at hn
  set w : ℝ := ((sz0.W n : ℕ) : ℝ) with hwdef
  set X : ℝ := ((sz0.size n : ℕ) : ℝ) ^ (1 / 18 : ℝ) with hXdef
  have h1 : (w⁻¹) ^ 2 * w ^ 3 ≤ 4 * X * (w ^ 3)⁻¹ * w ^ 3 :=
    mul_le_mul_of_nonneg_right hn (by positivity)
  have e1 : (w⁻¹) ^ 2 * w ^ 3 = w := by field_simp
  have e2 : 4 * X * (w ^ 3)⁻¹ * w ^ 3 = 4 * X := by field_simp
  have hwX : w ≤ 4 * X := by linarith
  have hm5 : m ≤ m ^ 5 / 16 := by
    have : 16 * m ≤ m ^ 5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm 4]
    linarith
  rw [hW] at hwX
  nlinarith

end Instances

end RBM.Green
