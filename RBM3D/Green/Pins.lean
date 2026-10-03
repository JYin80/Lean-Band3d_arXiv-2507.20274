/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs

/-!
# The `lem_GbEXP` pins and their bridges to the ST pins (ST-1, S1-07)

Ticket T2028 (S1-07).  Port of `RBM2D/Green/Pins.lean` at `c9a24cf` (gate P7e, row G0.1) with the
common renaming (R1-R3 of `docs/tickets/ST1-COMMON.md`), plus the bridges between the RBM2D forms
of the pins and the ST pins of `RBM3D/Induction/Defs.lean`.

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem_GbEXP` (`3_5:14`),
`(def_asGMc)` (`3_5:16`), `(GiiGEX)` (`3_5:21`), `(GijGEX)` (`3_5:24`), `(initialGT2)` (`3_5:30`),
`(GavLGEX)` (`3_5:33`).

* 1. Matrix-level vocabulary on the fine lattice `Idx d L W` (RBM2D `Path/Step2Vocab`,
  `Path/Step2Props`, `Green/Pins` section 1): `llErrMat`, `loopPM`, `greenBlk`, `avgErr`,
  `maxLoopPM`, `gexRHS`, `omegaInd`, `offSq`, `diagSq`, and `Sizes.RangeCond`.
* 2-4. The per-sequence components, the pins `GbEXPHypV3`, `GbEXPV3Theorem`, `GavLGEXRandHyp`, the
  per-time consumer shapes `GijGEXPTSwap`, `GiiGEXPT`, `AsGMcPT` and their bridges
  (`perTime_timeIcc_of_forall_seq`, `perSeq_of_perTime_timeIcc`, `gijGEXPTSwap_giiGEXPT_of_V3`).
* 5-6. Private lemmas: the two-loop in entries, the loop floor, the unit-ball count, `≺` reindexing.
* 7. **The bridges to the ST pins**: the equivalences `asGMcSeq_iff_prec`,
  `asGMcPT_iff_forall_prec`, `gavLDetSeq_iff_prec`; `loopDetSeq_of_prec` and
  `prec_maxLoop2_of_loopDetSeq`;
  `stGijGEX_of_gijOmegaSeq`, `giiOmegaSeq_of_stGiiGEX`, `stGiiGEX_of_omegaSeq`,
  `stGavLGEX_of_v3`, the flow parametrization `v3_premises_of_stFlow`, and
  `stGbEXP_of_v3 : GbEXPV3Theorem d → STGbEXP d`.
* 8. The extreme-input checks of RBM2D (`t ≡ 0`, `W = 1`), with `llErrMat_time_zero` and
  `asGMcSeq_time_zero` added.
* 9. Compiled nonempty instances at `d = 3` (`RBM.Green.Instance`).

Differences from RBM2D (every other ported statement equals RBM2D's after the renaming): (R1)
`SizeTendsto d → Bandwidth d 𝔠 →` is `sz.Admissible 𝔠 𝔡 →`, with the new constant `𝔡` after `𝔠`
(the coupling window `(eq:WO)`; RBM2D has no coupling); (R2) entries of the resolvent are indexed
by the fine lattice `Idx d L W` instead of `BlockIndex L W`, the block label is `STblk`/`split`;
(R3) `MainIndHyp` is replaced by `STFlow` (`v3_premises_of_stFlow`); (R4) the `W = 1` instance of
RBM2D is replaced by the preflight sequence `sz0`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

/-- The application range `1 - t ≥ N^{-1+δ}`, eventually (RBM2D `Path/Step2Props.lean:121`,
`RangeCond`, written there with the RBM2D paper's `1-2:990`).  Not a hypothesis of `lem:main_ind`
in the paper; RBM2D T2005 adds it. -/
def RangeCond (δ : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n

end RBM.Gauss.Sizes

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Loop
open scoped NNReal ENNReal

/-! ## 1. Matrix-level pieces -/

section MatrixLevel

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `|(G_u - m)_{ij}|` at the matrix `M` (the entries of `‖G_u - m‖_max`), spectral parameter
`z_u^{(E)}`.  RBM2D `Path/Step2Props.lean:98`; the merged `Gres M z true` is `(M - z)⁻¹`. -/
def llErrMat (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) : ℝ :=
  ‖Gres M (zt E u) true i j - (if i = j then mE E else 0)‖

/-- `𝓛_{u,(+,-),(a,b)}` at the matrix `M` (`Eq:defGLoop`, `1_2:824`).  RBM2D
`Path/Step2Vocab.lean:36`. -/
def loopPM (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) : ℂ :=
  loopFine d L W M (zt E u) ![true, false] ![a, b]

/-- The block-level resolvent `G_u(σ) = (blockMat M - z_u^{(E)}(σ))⁻¹` of `M`, on the block-product
index.  RBM2D `Path/Step2Vocab.lean:44`. -/
def greenBlk (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Gres (blockMat d L W M) (zt E u) σ

/-- `⟨G̃_u(σ) E_a⟩ = tr((G_u(σ) - m(σ)) E_a)` (`def_EwtG`, `1_2:735`; `⟨A⟩ = tr A`).  RBM2D
`Path/Step2Vocab.lean:49`. -/
def avgErr (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (σ : Bool) (a : Zd d L) : ℂ :=
  Matrix.trace ((greenBlk d L W E u M σ -
    mSigma E σ • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Eblk d L W a)

/-- `max_{a,b} |𝓛_{u,(+,-),(a,b)}|` at `M`.  RBM2D `Path/Step2Vocab.lean:77`. -/
def maxLoopPM (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d L), (0 : Zd d L)), Finset.mem_univ _⟩
    (fun p : Zd d L × Zd d L => ‖loopPM d L W E u M p.1 p.2‖)

/-- The right side of (`GijGEX`), `3_5:24`, at blocks `a, b`, in the one-orientation form of RBM2D
`Path/Step2Vocab.lean:81` (`gexRHS`; the pair is swapped in the pins, T2066a), with the `L^∞`
distance of the paper and `W^{-d}`. -/
def gexRHS (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) : ℝ :=
  (∑ a' : Zd d L, ∑ b' : Zd d L,
      if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then ‖loopPM d L W E u M a' b'‖
      else 0) +
    if zdistInf d L (a - b) ≤ 1 then ((W : ℝ) ^ d)⁻¹ else 0

/-- The indicator of `Ω(u,c) = {‖G_u - m‖_max ≤ W^{-c}}` (`def_asGMc`, `3_5:16`) at the matrix
`M`, spectral parameter `z_u^{(E)}`. -/
def omegaInd (E u c : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℝ :=
  if ∀ i j : Idx d L W, llErrMat d L W E u M i j ≤ (W : ℝ) ^ (-c) then 1 else 0

/-- `|G_{pq}|²` off the diagonal, `0` on it (left side of (`GijGEX`), `3_5:24`, with the
restriction `p ≠ q`).  The entries of `G` are on the fine lattice `Z_{WL}^d` (RBM2D:
`BlockIndex L W`, the block-product index of the same resolvent). -/
def offSq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p q : Idx d L W) : ℝ :=
  if p = q then 0 else ‖Gres M (zt E u) true p q‖ ^ 2

/-- `|G_{pp} - m|²` (left side of (`GiiGEX`), `3_5:21`, on the diagonal). -/
def diagSq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (p : Idx d L W) : ℝ :=
  ‖Gres M (zt E u) true p p - mE E‖ ^ 2

end MatrixLevel

/-! ## 2. Per-sequence components (time `t n`, energy `E n` at size index `n`) -/

section Components

variable {d : ℕ} (sz : Sizes d)

/-- (`GijGEX`), `3_5:24`, on `Ω(t,c)` (`def_asGMc`, `3_5:16`), off the diagonal, right side with the
swapped pair (RBM2D T2066a).  Component of `GbEXPHypV3`.  RBM2D `Green/Pins.lean:68`. -/
def GijOmegaSeq (E t : ℕ → ℝ) (c : ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
      offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2)
    (fun n p ω => gexRHS d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)
      (STblk sz n p.2.2) (STblk sz n p.2.1))

/-- (`GiiGEX`), `3_5:21`, on `Ω(t,c)`, diagonal entries.  Component of `GbEXPHypV3`.  RBM2D
`Green/Pins.lean:77`. -/
def GiiOmegaSeq (E t : ℕ → ℝ) (c : ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n))
    (fun n p ω => omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
      diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2)
    (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))

/-- (`asGMc`), `3_5:30` (`(initialGT2)`, first part): `‖G_t - m‖_max ≺ W^{-c}`.  Hypothesis inside
`GbEXPHypV3` and `GavLGEXRandHyp`.  RBM2D `Green/Pins.lean:85`. -/
def AsGMcSeq (E t : ℕ → ℝ) (c : ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2)
    (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c))

/-- (`GijGEX`), `3_5:24`, without the indicator under (`asGMc`), off the diagonal, swapped right
side.  Component of `GbEXPHypV3`.  RBM2D `Green/Pins.lean:94`. -/
def GijSeq (E t : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2)
    (fun n p ω => gexRHS d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)
      (STblk sz n p.2.2) (STblk sz n p.2.1))

/-- (`GiiGEX`), `3_5:21`, without the indicator under (`asGMc`), diagonal entries.  Component of
`GbEXPHypV3`.  RBM2D `Green/Pins.lean:102`. -/
def GiiSeq (E t : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Idx d (sz.L n) (sz.W n))
    (fun n p ω => diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2)
    (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))

/-- `max_{a,b} |𝓛_{t,(+,-),(a,b)}| ≺ Ψ²` for a deterministic `Ψ` (the second part of
`(initialGT2)`, `3_5:30`, read with `|𝓛_{(+,-),(a,b)}| = |𝓛_{(-,+),(b,a)}|`).  Hypothesis of the
(`GavLGEX`) clause of `GbEXPHypV3`.  RBM2D `Green/Pins.lean:111`. -/
def LoopDetSeq (E t : ℕ → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖loopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2‖)
    (fun n _ _ => Ψ n ^ 2)

/-- (`GavLGEX`), `3_5:33`, with a deterministic control `Ψ²`: `max_a |⟨(G_t - m) E_a⟩| ≺ Ψ²`.
Component of `GbEXPHypV3`.  RBM2D `Green/Pins.lean:119`. -/
def GavLDetSeq (E t : ℕ → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Zd d (sz.L n))
    (fun n p ω => ‖avgErr d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true p.2‖)
    (fun n _ _ => Ψ n ^ 2)

/-- (`GavLGEX`), `3_5:33`, as displayed in RBM2D: random control `max_{a,b} 𝓛_{t,(+,-),(a,b)}`.
Component of `GavLGEXRandHyp`.  RBM2D `Green/Pins.lean:126`. -/
def GavLRandSeq (E t : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => Unit × Zd d (sz.L n))
    (fun n p ω => ‖avgErr d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) true p.2‖)
    (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω))

end Components

/-! ## 3. The pins -/

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **Pin `GbEXPHypV3`** (`lem_GbEXP`, `3_5:14-40`; RBM2D `Green/Pins.lean:152`).  Fixed `κ` (bulk),
`𝔠` (bandwidth, `(Main_DEL_COND)`, `1_2:359`), `𝔡` (the window `(eq:WO)`, `1_2:363`), `δ` (range
`1 - t ≥ N^{-1+δ}`), then the size data, every energy and time sequence in the bulk with the range
condition, and every `c > 0`:
* (`GijGEX`) on `Ω(t,c)`, off the diagonal, right side `Σ_{a'∼a} Σ_{b'∼b} 𝓛_{(+,-),(b',a')} +
  W^{-d} 1(|a-b| ≤ 1)` (swapped pair, RBM2D T2066a);
* (`GiiGEX`) on `Ω(t,c)`, diagonal entries;
* under (`asGMc`) at `c`: (`GijGEX`), (`GiiGEX`) without the indicator, and (`GavLGEX`) in the
  deterministic-control form: `max 𝓛 ≺ Ψ²` with `0 ≤ Ψ ≤ N^{-a}` gives `max_a |⟨(G-m)E_a⟩| ≺ Ψ²`.
The hypotheses `SizeTendsto d → Bandwidth d 𝔠` of RBM2D are `sz.Admissible 𝔠 𝔡`, which adds the
coupling window `(eq:WO)` of the paper's random band matrix model (RBM2D has no coupling). -/
def GbEXPHypV3 (κ 𝔠 𝔡 δ : ℝ) : Prop :=
  sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t →
  ∀ c > (0 : ℝ),
    GijOmegaSeq sz E t c ∧ GiiOmegaSeq sz E t c ∧
    (AsGMcSeq sz E t c →
      GijSeq sz E t ∧ GiiSeq sz E t ∧
      ∀ (Ψ : ℕ → ℝ) (a : ℝ), 0 < a → (∀ n, 0 ≤ Ψ n) →
        (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
        LoopDetSeq sz E t Ψ → GavLDetSeq sz E t Ψ)

/-- **Pin `GbEXPV3Theorem`** (the P7e deliverable; `lem_GbEXP`, `3_5:14-40`; RBM2D
`Green/Pins.lean:166`): `GbEXPHypV3` for every size sequence of dimension `d` and every
`κ, 𝔠, 𝔡, δ > 0`. -/
def GbEXPV3Theorem (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (κ 𝔠 𝔡 δ : ℝ), 0 < κ → 0 < 𝔠 → 0 < 𝔡 → 0 < δ → GbEXPHypV3 sz κ 𝔠 𝔡 δ

/-- **Pin `GavLGEXRandHyp`** (`GavLGEX`, `3_5:33`, as displayed: random control `max 𝓛`).  Not part
of `GbEXPHypV3`.  RBM2D `Green/Pins.lean:173`. -/
def GavLGEXRandHyp (κ 𝔠 𝔡 δ : ℝ) : Prop :=
  sz.Admissible 𝔠 𝔡 →
  ∀ E t : ℕ → ℝ, (∀ n, |E n| < 2 - κ) → (∀ n, 0 ≤ t n) → (∀ n, t n < 1) → sz.RangeCond δ t →
  ∀ c > (0 : ℝ), AsGMcSeq sz E t c → GavLRandSeq sz E t

end Pins

/-! ## 4. Consumer shapes and bridges -/

section Bridges

/-- **Bridge (proved): per sequence ⇒ per time over `[s,t]`.**  If a bound holds per sequence at
every time sequence `u n ∈ [s n, t n]`, it holds per time over `TimeIcc s t` (merged
`RBM.Path.perTimeDomAt_iff_forall_section`, used twice).  RBM2D `Green/Pins.lean:187`. -/
theorem perTime_timeIcc_of_forall_seq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) {V : ℕ → Type*}
    (hV : ∀ n, Nonempty (V n)) (ξ ζ : ∀ n, ℝ → V n → Ω → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      PerTimeDomAt P size (U := fun n => Unit × V n)
        (fun n p ω => ξ n (u n) p.2 ω) (fun n p ω => ζ n (u n) p.2 ω)) :
    PerTimeDomAt P size (U := fun n => TimeIcc s t n × V n)
      (fun n p ω => ξ n p.1 p.2 ω) (fun n p ω => ζ n p.1 p.2 ω) := by
  have hne : ∀ n, Nonempty (TimeIcc s t n × V n) :=
    fun n => ⟨(⟨s n, le_rfl, hst n⟩, (hV n).some)⟩
  rw [perTimeDomAt_iff_forall_section P size hne]
  intro sec
  have h1 := h (fun n => ((sec n).1 : ℝ)) (fun n => (sec n).1.2)
  have hne' : ∀ n, Nonempty (Unit × V n) := fun n => ⟨((), (hV n).some)⟩
  rw [perTimeDomAt_iff_forall_section P size hne'] at h1
  exact h1 (fun n => ((), (sec n).2))

/-- **Bridge (proved): per time over `[s,t]` ⇒ per sequence at any section time sequence.**
RBM2D `Green/Pins.lean:205`. -/
theorem perSeq_of_perTime_timeIcc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {s t : ℕ → ℝ} {V : ℕ → Type*} (hV : ∀ n, Nonempty (V n))
    (ξ ζ : ∀ n, ℝ → V n → Ω → ℝ)
    (h : PerTimeDomAt P size (U := fun n => TimeIcc s t n × V n)
      (fun n p ω => ξ n p.1 p.2 ω) (fun n p ω => ζ n p.1 p.2 ω))
    (u : ℕ → ℝ) (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) :
    PerTimeDomAt P size (U := fun n => Unit × V n)
      (fun n p ω => ξ n (u n) p.2 ω) (fun n p ω => ζ n (u n) p.2 ω) := by
  have hne : ∀ n, Nonempty (TimeIcc s t n × V n) :=
    fun n => ⟨(⟨u n, hu n⟩, (hV n).some)⟩
  have hne' : ∀ n, Nonempty (Unit × V n) := fun n => ⟨((), (hV n).some)⟩
  rw [perTimeDomAt_iff_forall_section P size hne] at h
  rw [perTimeDomAt_iff_forall_section P size hne']
  intro sec
  exact h (fun n => (⟨u n, hu n⟩, (sec n).2))

variable {d : ℕ} (sz : Sizes d)

/-- (`GijGEX`), `3_5:24`, per time over `[s,t]`, off the diagonal, with the swapped pair of
`gexRHS` (RBM2D T2049 `GijGEXPT` with `gexRHS` arguments swapped, T2066a).  RBM2D
`Green/Pins.lean:227`. -/
def GijGEXPTSwap (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => if p.2.1 = p.2.2 then 0 else ‖Gt sz n (E n) p.1 true ω p.2.1 p.2.2‖ ^ 2)
    (fun n p ω => gexRHS d (sz.L n) (sz.W n) (E n) p.1 (sz.seqHflow n p.1 ω)
      (STblk sz n p.2.2) (STblk sz n p.2.1))

/-- (`GiiGEX`), `3_5:21`, per time over `[s,t]`, diagonal entries.  RBM2D `Green/Pins.lean:236`. -/
def GiiGEXPT (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  sz.PrecPT (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖Gt sz n (E n) p.1 true ω p.2 p.2 - mE (E n)‖ ^ 2)
    (fun n p ω => maxLoopPM d (sz.L n) (sz.W n) (E n) p.1 (sz.seqHflow n p.1 ω))

/-- (`asGMc`), `3_5:30`, per time over `[s,t]`, at exponent `c`.  Hypothesis of
`gijGEXPTSwap_giiGEXPT_of_V3`.  RBM2D `Green/Pins.lean:246`. -/
def AsGMcPT (E : ℕ → ℝ) (s t : ℕ → ℝ) (c : ℝ) : Prop :=
  sz.PrecPT (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => llErrMat d (sz.L n) (sz.W n) (E n) p.1 (sz.seqHflow n p.1 ω) p.2.1 p.2.2)
    (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c))

/-- `RangeCond` passes to any time sequence below `t`.  RBM2D `Green/Pins.lean:253`. -/
theorem rangeCond_mono {δ : ℝ} {t u : ℕ → ℝ} (h : sz.RangeCond δ t) (hut : ∀ n, u n ≤ t n) :
    sz.RangeCond δ u :=
  h.mono fun n hn => hn.trans (by linarith [hut n])

/-- **Bridge (proved): `GbEXPHypV3` ⇒ the per-time (`GijGEX`) (swapped) and (`GiiGEX`)**, given
(`asGMc`) per time over `[s,t]` (the calling row derives it from (`Gtmwc`) and `RangeCond`).
RBM2D `Green/Pins.lean:260`. -/
theorem gijGEXPTSwap_giiGEXPT_of_V3 {κ 𝔠 𝔡 δ c : ℝ} {E s t : ℕ → ℝ}
    (hV3 : GbEXPHypV3 sz κ 𝔠 𝔡 δ) (hA : sz.Admissible 𝔠 𝔡)
    (hE : ∀ n, |E n| < 2 - κ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1)
    (hR : sz.RangeCond δ t) (hc : 0 < c) (hAs : AsGMcPT sz E s t c) :
    GijGEXPTSwap sz E s t ∧ GiiGEXPT sz E s t := by
  have hseq : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      GijSeq sz E u ∧ GiiSeq sz E u := by
    intro u hu
    have hRu : sz.RangeCond δ u := rangeCond_mono sz hR fun n => (hu n).2
    have hAsu : AsGMcSeq sz E u c :=
      perSeq_of_perTime_timeIcc sz.seqP sz.size
        (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
        (fun n => ⟨(0, 0)⟩)
        (fun n v q ω => llErrMat d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω) q.1 q.2)
        (fun n _ _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c)) hAs u hu
    have h := (hV3 hA E u hE (fun n => (hs n).trans (hu n).1)
      (fun n => (hu n).2.trans_lt (ht n)) hRu c hc).2.2 hAsu
    exact ⟨h.1, h.2.1⟩
  refine ⟨?_, ?_⟩
  · exact perTime_timeIcc_of_forall_seq sz.seqP sz.size hst
      (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => offSq d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω) q.1 q.2)
      (fun n v q ω => gexRHS d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω)
        (STblk sz n q.2) (STblk sz n q.1))
      fun u hu => (hseq u hu).1
  · exact perTime_timeIcc_of_forall_seq sz.seqP sz.size hst
      (V := fun n => Idx d (sz.L n) (sz.W n)) (fun n => ⟨0⟩)
      (fun n v q ω => diagSq d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω) q)
      (fun n v _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω))
      fun u hu => (hseq u hu).2

end Bridges

/-! ## 5. Deterministic toolbox (private lemmas) -/

section Toolbox

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

omit [NeZero L] [NeZero W] in
private theorem gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)
    (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  rfl

omit [NeZero W] in
private theorem trace_pm_formula (G : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a b : Zd d L) :
    ((G * Eblk d L W a) * (Gᴴ * Eblk d L W b)).trace =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ v : Vtx d L W, ∑ w : Vtx d L W,
          (if v.1 = b ∧ w.1 = a then ‖G v w‖ ^ 2 else 0) : ℝ) : ℂ) := by
  have hE : ∀ c : Zd d L, Eblk d L W c = Matrix.diagonal fun x : Vtx d L W =>
      if x.1 = c then (((W : ℂ)) ^ d)⁻¹ else 0 := fun c => rfl
  rw [hE a, hE b]
  have h1 : G * Matrix.diagonal (fun x : Vtx d L W => if x.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => G i j * (if j.1 = a then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal]
  have h2 : Gᴴ * Matrix.diagonal (fun x : Vtx d L W => if x.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) =
      Matrix.of fun i j => star (G j i) * (if j.1 = b then (((W : ℂ)) ^ d)⁻¹ else 0) := by
    ext i j; simp [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [h1, h2]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : i.1 = b <;> by_cases hj : j.1 = a <;> simp [hi, hj]
  have h := Complex.mul_conj' (G i j)
  linear_combination (((W : ℂ) ^ d)⁻¹) ^ 2 * h

/-- The two-loop on the block-product index: `𝓛_{(+,-),(a,b)} = W^{-2d} Σ_{v∈[b], w∈[a]} |G_{vw}|²`
(rows in block `b`, columns in block `a`), for a Hermitian `H`. -/
private theorem loopFine_pm_formula_vtx (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (hH : H.IsHermitian) (z : ℂ) (a b : Zd d L) :
    loopFine d L W H z ![true, false] ![a, b] =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ v : Vtx d L W, ∑ w : Vtx d L W,
          (if v.1 = b ∧ w.1 = a then ‖Gres (blockMat d L W H) z true v w‖ ^ 2 else 0) : ℝ) : ℂ) := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  rw [gres_false _ hHb z, trace_pm_formula]

/-- **The two-loop in entries** (RBM2D `norm_loopPM_eq`, `Green/Pins.lean:406`, in `d` dimensions):
for a Hermitian `H`, `𝓛_{(+,-),(a,b)} = W^{-2d} Σ_{y∈[b], x∈[a]} |G_{yx}|²` (rows in block `b`,
columns in block `a`), on the fine lattice. -/
private theorem loopFine_pm_formula (H : Matrix (Idx d L W) (Idx d L W) ℂ) (hH : H.IsHermitian)
    (z : ℂ) (a b : Zd d L) :
    loopFine d L W H z ![true, false] ![a, b] =
      ((((W : ℝ) ^ d)⁻¹ ^ 2 * ∑ y : Idx d L W, ∑ x : Idx d L W,
          (if (split d L W y).1 = b ∧ (split d L W x).1 = a then ‖Gres H z true y x‖ ^ 2
            else 0) : ℝ) : ℂ) := by
  rw [loopFine_pm_formula_vtx H hH z a b]
  congr 1
  congr 1
  have hsum : ∀ F : Vtx d L W → Vtx d L W → ℝ, ∑ v, ∑ w, F v w =
      ∑ y : Idx d L W, ∑ x : Idx d L W, F (splitEquiv d L W y) (splitEquiv d L W x) := by
    intro F
    calc ∑ v, ∑ w, F v w = ∑ y, ∑ w, F (splitEquiv d L W y) w :=
          (Equiv.sum_comp (splitEquiv d L W) (fun v => ∑ w, F v w)).symm
      _ = _ := Finset.sum_congr rfl fun y _ =>
          (Equiv.sum_comp (splitEquiv d L W) (fun w => F (splitEquiv d L W y) w)).symm
  rw [hsum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [gres_blockMat_true, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

private theorem norm_loopPM_le_max (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a b : Zd d L) : ‖loopPM d L W E u M a b‖ ≤ maxLoopPM d L W E u M :=
  Finset.le_sup' (fun p : Zd d L × Zd d L => ‖loopPM d L W E u M p.1 p.2‖) (Finset.mem_univ (a, b))

/-- **The loop floor** (RBM2D `inv_W2_le_maxLoopPM`, `Green/EntryBlock.lean:430`, in `d`
dimensions): on `Ω(u,c)` with `W^{-c} ≤ 1/2`, `W^{-d} ≤ 4 max_{a,b} |𝓛_{(+,-),(a,b)}|`; the
diagonal entries alone contribute `≥ W^{-d}/4` to `𝓛_{(+,-),(0,0)}`. -/
private theorem inv_W_pow_le_maxLoopPM {E u c : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hE : |E| ≤ 2) (hM : M.IsHermitian) (hc : (W : ℝ) ^ (-c) ≤ 1 / 2)
    (hΩ : ∀ i j : Idx d L W, llErrMat d L W E u M i j ≤ (W : ℝ) ^ (-c)) :
    ((W : ℝ) ^ d)⁻¹ ≤ 4 * maxLoopPM d L W E u M := by
  have hW : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hW d
  have hdiag : ∀ y : Idx d L W, (1 : ℝ) / 4 ≤ ‖Gres M (zt E u) true y y‖ ^ 2 := by
    intro y
    have h1 := hΩ y y
    unfold llErrMat at h1
    simp only [ite_true] at h1
    have hm := norm_mE hE
    have h2 : ‖mE E‖ ≤ ‖Gres M (zt E u) true y y‖ + ‖Gres M (zt E u) true y y - mE E‖ := by
      have := norm_sub_le (Gres M (zt E u) true y y) (Gres M (zt E u) true y y - mE E)
      rwa [sub_sub_cancel] at this
    have h3 : (1 : ℝ) / 2 ≤ ‖Gres M (zt E u) true y y‖ := by linarith
    nlinarith
  set G := Gres M (zt E u) true with hG
  have hS : (W : ℝ) ^ d / 4 ≤ ∑ y : Idx d L W, ∑ x : Idx d L W,
      (if (split d L W y).1 = 0 ∧ (split d L W x).1 = 0 then ‖G y x‖ ^ 2 else 0) := by
    calc (W : ℝ) ^ d / 4
        = ∑ y : Idx d L W, (if (split d L W y).1 = 0 then (1 : ℝ) / 4 else 0) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have := card_Iblk d L W (0 : Zd d L)
          simp only [Iblk] at this
          rw [this]; push_cast; ring
      _ ≤ _ := by
          refine Finset.sum_le_sum fun y _ => ?_
          split_ifs with hy
          · calc (1 : ℝ) / 4 ≤ ‖G y y‖ ^ 2 := hdiag y
              _ = (if (split d L W y).1 = 0 ∧ (split d L W y).1 = 0 then ‖G y y‖ ^ 2 else 0) := by
                  simp [hy]
              _ ≤ _ := Finset.single_le_sum
                  (f := fun x => if (split d L W y).1 = 0 ∧ (split d L W x).1 = 0 then
                    ‖G y x‖ ^ 2 else 0)
                  (fun x _ => by split_ifs <;> positivity) (Finset.mem_univ y)
          · exact Finset.sum_nonneg fun x _ => by split_ifs <;> positivity
  have hL : ((W : ℝ) ^ d)⁻¹ / 4 ≤ ‖loopPM d L W E u M 0 0‖ := by
    unfold loopPM
    rw [loopFine_pm_formula M hM (zt E u) 0 0, Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => by
        split_ifs <;> positivity))]
    calc ((W : ℝ) ^ d)⁻¹ / 4 = (((W : ℝ) ^ d)⁻¹) ^ 2 * ((W : ℝ) ^ d / 4) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (by positivity)
  have h5 := norm_loopPM_le_max (d := d) (L := L) (W := W) E u M 0 0
  linarith

private theorem loopFine_mp_eq_pm (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (a b : Zd d L) :
    loopFine d L W H z ![false, true] ![a, b] = loopFine d L W H z ![true, false] ![b, a] := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact Matrix.trace_mul_comm _ _

private theorem zdistInf_neg (d L : ℕ) [NeZero L] (x : Zd d L) :
    zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem zdist_le_one {L : ℕ} [NeZero L] {y : ZMod L} (h : zdist L y ≤ 1) :
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

/-- The `L^∞` unit ball of `Z_L^d` has at most `3^d` points. -/
private theorem card_ball_le (d L : ℕ) [NeZero L] (a : Zd d L) :
    (Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1).card ≤ 3 ^ d := by
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
    rcases zdist_le_one h1 with h | h | h <;> simp [T, h]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => T).card := Finset.card_image_le
    _ = T.card ^ d := by simp [Fintype.card_piFinset]
    _ ≤ 3 ^ d := Nat.pow_le_pow_left hT d

private theorem double_sum_ite {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop) (B : β → Prop)
    [DecidablePred A] [DecidablePred B] (m : ℝ) :
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

/-- `gexRHS ≤ 9^d max𝓛 + W^{-d}`: the two unit balls have at most `3^d` points each. -/
private theorem gexRHS_le_ball (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) :
    gexRHS d L W E u M a b ≤ (9 : ℝ) ^ d * maxLoopPM d L W E u M + ((W : ℝ) ^ d)⁻¹ := by
  have hmax : ∀ a' b' : Zd d L, ‖loopPM d L W E u M a' b'‖ ≤ maxLoopPM d L W E u M :=
    fun a' b' => norm_loopPM_le_max E u M a' b'
  have hm0 : 0 ≤ maxLoopPM d L W E u M := (norm_nonneg _).trans (hmax 0 0)
  unfold gexRHS
  refine add_le_add ?_ ?_
  · calc (∑ a' : Zd d L, ∑ b' : Zd d L,
          if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
            ‖loopPM d L W E u M a' b'‖ else 0)
        ≤ ∑ a' : Zd d L, ∑ b' : Zd d L,
          if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
            maxLoopPM d L W E u M else 0 := by
          refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
          split_ifs
          · exact hmax a' b'
          · exact le_rfl
      _ = ((Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1).card : ℝ) *
          (((Finset.univ.filter fun x : Zd d L => zdistInf d L (x - b) ≤ 1).card : ℝ) *
            maxLoopPM d L W E u M) :=
          double_sum_ite (fun x : Zd d L => zdistInf d L (x - a) ≤ 1)
            (fun x : Zd d L => zdistInf d L (x - b) ≤ 1) _
      _ ≤ (3 ^ d : ℝ) * ((3 ^ d : ℝ) * maxLoopPM d L W E u M) := by
          have h1 : ((Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1).card : ℝ) ≤
              (3 ^ d : ℝ) := by exact_mod_cast card_ball_le d L a
          have h2 : ((Finset.univ.filter fun x : Zd d L => zdistInf d L (x - b) ≤ 1).card : ℝ) ≤
              (3 ^ d : ℝ) := by exact_mod_cast card_ball_le d L b
          gcongr
      _ = (9 : ℝ) ^ d * maxLoopPM d L W E u M := by
          rw [← mul_assoc, ← mul_pow]; norm_num
  · split_ifs
    · exact le_rfl
    · positivity

private theorem sum_sum_ite_and {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop) (B : β → Prop)
    [DecidablePred A] [DecidablePred B] (f : α → β → ℝ) :
    ∑ a : α, ∑ b : β, (if A a ∧ B b then f a b else 0) =
      ∑ a ∈ Finset.univ.filter A, ∑ b ∈ Finset.univ.filter B, f a b := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : A a
  · simp only [ha, true_and, ite_true]
    rw [Finset.sum_filter]
  · simp [ha]

end Toolbox

section ModelLevel

variable {d : ℕ} (sz : Sizes d)

private theorem stmaxLoop2_eq_maxLoopPM (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) :
    STmaxLoop2 sz n E τ ω = maxLoopPM d (sz.L n) (sz.W n) E τ (sz.seqHflow n τ ω) := by
  unfold STmaxLoop2 maxLoopPM
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun p _ => ?_
    have h : ‖Lloop sz n E τ ![false, true] ![p.1, p.2] ω‖ =
        ‖loopPM d (sz.L n) (sz.W n) E τ (sz.seqHflow n τ ω) p.2 p.1‖ := by
      unfold Lloop loopPM
      rw [loopFine_mp_eq_pm]
    rw [h]
    exact Finset.le_sup' (fun q : Zd d (sz.L n) × Zd d (sz.L n) =>
      ‖loopPM d (sz.L n) (sz.W n) E τ (sz.seqHflow n τ ω) q.1 q.2‖) (Finset.mem_univ (p.2, p.1))
  · refine Finset.sup'_le _ _ fun p _ => ?_
    have h : ‖loopPM d (sz.L n) (sz.W n) E τ (sz.seqHflow n τ ω) p.1 p.2‖ =
        ‖Lloop sz n E τ ![false, true] ![p.2, p.1] ω‖ := by
      unfold Lloop loopPM
      rw [loopFine_mp_eq_pm]
    rw [h]
    exact Finset.le_sup' (fun q : Zd d (sz.L n) × Zd d (sz.L n) =>
      ‖Lloop sz n E τ ![false, true] ![q.1, q.2] ω‖) (Finset.mem_univ (p.2, p.1))

private theorem gexRHS_swap_le (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    gexRHS d (sz.L n) (sz.W n) E τ (sz.seqHflow n τ ω) b a ≤ STgexRHS sz n E τ ω a b := by
  unfold gexRHS STgexRHS
  have hne : (![true, false] : Fin 2 → Bool) ≠ ![false, true] := by decide
  rw [Finset.sum_pair hne]
  rw [sum_sum_ite_and (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - b) ≤ 1)
    (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - a) ≤ 1)
    (fun a' b' => ‖loopPM d (sz.L n) (sz.W n) E τ (sz.seqHflow n τ ω) a' b'‖)]
  have hswap : ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - b) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - a) ≤ 1),
        ‖loopPM d (sz.L n) (sz.W n) E τ (sz.seqHflow n τ ω) a' b'‖ =
      ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
        ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
          ‖sz.Lloop n E τ ![false, true] ![a', b'] ω‖ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    unfold Lloop loopPM
    rw [loopFine_mp_eq_pm]
  have h0 : 0 ≤ ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
        ‖sz.Lloop n E τ ![true, false] ![a', b'] ω‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hlast : (if zdistInf d (sz.L n) (b - a) ≤ 1 then (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ else 0) =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0) := by
    rw [← neg_sub a b, zdistInf_neg]
    split_ifs <;> simp
  rw [hswap, hlast]
  linarith

end ModelLevel

/-! ## 6. The `≺` toolbox: reindexing and monotonicity (private lemmas) -/

section StochTools

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U V : ℕ → Type*}

/-- Reindexing and monotonicity of the per-time domination: a smaller family along a map `φ` of
parameters, against a larger control. -/
private theorem perTimeDomAt_mono {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ' ζ' : ∀ l, V l → Ω → ℝ}
    (φ : ∀ l, V l → U l) (h : PerTimeDomAt P size ξ ζ)
    (hξ : ∀ᶠ l in atTop, ∀ v ω, ξ' l v ω ≤ ξ l (φ l v) ω)
    (hζ : ∀ᶠ l in atTop, ∀ v ω, ζ l (φ l v) ω ≤ ζ' l v ω) :
    PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hξ, hζ] with l hl h1 h2 v
  refine le_trans (measure_mono ?_) (hl (φ l v))
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have hn : (0 : ℝ) ≤ (size l : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (size l : ℝ) ^ τ * ζ l (φ l v) ω ≤ (size l : ℝ) ^ τ * ζ' l v ω :=
        mul_le_mul_of_nonneg_left (h2 v ω) hn
    _ < ξ' l v ω := hω
    _ ≤ ξ l (φ l v) ω := h1 v ω

/-- The same for the uniform domination. -/
private theorem stochDomAt_mono {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ' ζ' : ∀ l, V l → Ω → ℝ}
    (φ : ∀ l, V l → U l) (h : StochDomAt P size ξ ζ)
    (hξ : ∀ᶠ l in atTop, ∀ v ω, ξ' l v ω ≤ ξ l (φ l v) ω)
    (hζ : ∀ᶠ l in atTop, ∀ v ω, ζ l (φ l v) ω ≤ ζ' l v ω) :
    StochDomAt P size ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hξ, hζ] with l hl h1 h2
  refine le_trans (measure_mono ?_) hl
  rintro ω ⟨v, hv⟩
  refine ⟨φ l v, ?_⟩
  have hn : (0 : ℝ) ≤ (size l : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (size l : ℝ) ^ τ * ζ l (φ l v) ω ≤ (size l : ℝ) ^ τ * ζ' l v ω :=
        mul_le_mul_of_nonneg_left (h2 v ω) hn
    _ < ξ' l v ω := hv
    _ ≤ ξ l (φ l v) ω := h1 v ω

/-- Uniform ⇒ per-time (each event is contained in the union). -/
private theorem perTimeDomAt_of_stochDomAt {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : StochDomAt P size ξ ζ) : PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine le_trans (measure_mono ?_) hl
  intro ω hω
  exact ⟨u, hω⟩

end StochTools

/-! ## 7. Bridges to the ST pins -/

section Bridge

variable {d : ℕ} (sz : Sizes d)

private theorem card_Zd (d L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

private theorem card_Zd_le_size (n : ℕ) : Fintype.card (Zd d (sz.L n)) ≤ sz.size n := by
  rw [card_Zd]
  unfold Sizes.size
  exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

private theorem card_Idx_real (n : ℕ) :
    ((Fintype.card (Idx d (sz.L n) (sz.W n)) : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) := by
  rw [Sizes.card_Idx]

private theorem card_Idx_prod_le (n : ℕ) :
    ((Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℕ) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [Fintype.card_prod, Nat.cast_mul, card_Idx_real, Real.rpow_two]
  ring_nf; exact le_rfl

private theorem card_Idx_le (n : ℕ) :
    ((Fintype.card (Idx d (sz.L n) (sz.W n)) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := by
  rw [card_Idx_real, Real.rpow_one]

/-- `(asGMc)` per sequence is the same as `‖G_t - M‖_max ≺ W^{-c}` at the scale `N`
(`≺` over the entries `(x,y)`): the union over `|Idx²| = N²` entries is absorbed. -/
theorem asGMcSeq_iff_prec (E t : ℕ → ℝ) (c : ℝ) :
    AsGMcSeq sz E t c ↔
      sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
        (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖)
        (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c)) := by
  constructor
  · intro h
    have h1 : sz.PrecPT (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
        (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖)
        (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c)) :=
      perTimeDomAt_mono (fun n (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => ((), p)) h
        (Eventually.of_forall fun n v ω => le_of_eq rfl)
        (Eventually.of_forall fun n v ω => le_rfl)
    exact Path.stochDomAt_of_perTimeDomAt sz.seqP sz.size (C := 2) (by norm_num)
      (Eventually.of_forall fun n => card_Idx_prod_le sz n) h1
  · intro h
    exact perTimeDomAt_mono
      (fun n (p : Unit × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => p.2)
      (perTimeDomAt_of_stochDomAt h)
      (Eventually.of_forall fun n v ω => le_of_eq rfl) (Eventually.of_forall fun n v ω => le_rfl)

/-- **`AsGMcPT` is `‖G_u - M‖_max ≺ W^{-c}` at every time sequence `u ∈ [s,t]`** (`(asGMc)`, `3_5:30`,
at each time of the ST pins, which are single-time statements): `asGMcSeq_iff_prec` at each section,
lifted with `perTime_timeIcc_of_forall_seq` and `perSeq_of_perTime_timeIcc`. -/
theorem asGMcPT_iff_forall_prec {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (c : ℝ) :
    AsGMcPT sz E s t c ↔
      ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
        sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖STGM sz n (E n) (u n) ω p.1 p.2‖)
          (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c)) := by
  constructor
  · intro h u hu
    refine (asGMcSeq_iff_prec sz E u c).1 ?_
    exact perSeq_of_perTime_timeIcc sz.seqP sz.size
      (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => llErrMat d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω) q.1 q.2)
      (fun n _ _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c)) h u hu
  · intro h
    exact perTime_timeIcc_of_forall_seq sz.seqP sz.size hst
      (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n => ⟨(0, 0)⟩)
      (fun n v q ω => llErrMat d (sz.L n) (sz.W n) (E n) v (sz.seqHflow n v ω) q.1 q.2)
      (fun n _ _ _ => ((sz.W n : ℕ) : ℝ) ^ (-c))
      fun u hu => (asGMcSeq_iff_prec sz E u c).2 (h u hu)

/-- **Bridge `GijOmegaSeq ⇒ STGijGEX`** (`(GijGEX)`, `3_5:24`).  The RBM2D form is per time (the
union over the entries outside `P`), off the diagonal, with the one-orientation right side
`gexRHS … [y] [x]`; the ST pin is uniform (`Prec`), over the pairs `x ≠ y`, with the right side
of the paper (both `σ ∈ {(+,-),(-,+)}`): the right side is monotone
(`gexRHS … [y] [x] ≤ STgexRHS … [x] [y]`, the `σ = (-,+)` terms are the `gexRHS` terms by
`|𝓛_{(-,+),(a,b)}| = |𝓛_{(+,-),(b,a)}|`) and the union over `≤ N²` pairs is absorbed.  The converse
is not derivable: `STgexRHS` has the extra `σ = (+,-)` terms. -/
theorem stGijGEX_of_gijOmegaSeq {E t : ℕ → ℝ} {c : ℝ} (h : GijOmegaSeq sz E t c) :
    STGijGEX sz E t c := by
  have h1 : sz.PrecPT
      (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
      (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-c)) ω *
        ‖Gt sz n (E n) (t n) true ω p.1.1 p.1.2‖ ^ 2)
      (fun n p ω => STgexRHS sz n (E n) (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2)) :=
    perTimeDomAt_mono
      (fun n (p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2}) =>
        ((), p.1)) h
      (Eventually.of_forall fun n v ω => by
        have hv : v.1.1 ≠ v.1.2 := v.2
        refine le_of_eq ?_
        simp only [omegaInd, offSq, hv, ↓reduceIte]
        rfl)
      (Eventually.of_forall fun n v ω =>
        gexRHS_swap_le sz n (E n) (t n) ω (STblk sz n v.1.1) (STblk sz n v.1.2))
  refine Path.stochDomAt_of_perTimeDomAt sz.seqP sz.size (C := 2) (by norm_num)
    (Eventually.of_forall fun n => ?_) h1
  refine le_trans ?_ (card_Idx_prod_le sz n)
  exact_mod_cast Fintype.card_subtype_le _

private theorem stGM_self (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (x : Idx d (sz.L n) (sz.W n)) :
    STGM sz n E τ ω x x = Gt sz n E τ true ω x x - mE E := by
  unfold STGM
  simp

private theorem omegaInd_eq (n : ℕ) (E u c : ℝ) (ω : sz.SeqΩ) :
    omegaInd d (sz.L n) (sz.W n) E u c (sz.seqHflow n u ω) =
      STindMax sz n E u (((sz.W n : ℕ) : ℝ) ^ (-c)) ω := rfl

private theorem diagSq_eq (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (x : Idx d (sz.L n) (sz.W n)) :
    diagSq d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) x = ‖STGM sz n E u ω x x‖ ^ 2 := by
  rw [stGM_self]
  rfl

/-- **Bridge `STGiiGEX ⇒ GiiOmegaSeq`**: the diagonal entries of the all-entries pin. -/
theorem giiOmegaSeq_of_stGiiGEX {E t : ℕ → ℝ} {c : ℝ} (h : STGiiGEX sz E t c) :
    GiiOmegaSeq sz E t c := by
  have h0 : sz.PrecPT (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-c)) ω *
        ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2)
      (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω) := perTimeDomAt_of_stochDomAt h
  refine perTimeDomAt_mono (fun n (p : Unit × Idx d (sz.L n) (sz.W n)) => (p.2, p.2)) h0
    (Eventually.of_forall fun n v ω => ?_)
    (Eventually.of_forall fun n v ω =>
      le_of_eq (stmaxLoop2_eq_maxLoopPM sz n (E n) (t n) ω))
  refine le_of_eq ?_
  show omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
      diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) v.2 = _
  rw [omegaInd_eq, diagSq_eq]

/-- `W → ∞` along an admissible sequence (`W ≥ N^𝔠` and `N → ∞`). -/
private theorem W_tendsto_of_admissible {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hN, hB, -⟩ := hA
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  exact tendsto_atTop_mono' atTop hB h1

private theorem eventually_W_rpow_neg_le {𝔠 𝔡 c : ℝ} (hA : sz.Admissible 𝔠 𝔡) (hc : 0 < c) :
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c) ≤ 1 / 2 := by
  have h := (tendsto_rpow_neg_atTop hc).comp (W_tendsto_of_admissible sz hA)
  exact (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun n hn => hn.le

private theorem stGM_ne (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {x y : Idx d (sz.L n) (sz.W n)}
    (hxy : x ≠ y) : STGM sz n E τ ω x y = Gt sz n E τ true ω x y := by
  unfold STGM
  simp [hxy]

/-- **Bridge `GiiOmegaSeq ∧ GijOmegaSeq ⇒ STGiiGEX`** (`(GiiGEX)`, `3_5:21`, all entries of
`G_t - M`).  The ST pin is the all-entries statement `1(Ω) ‖G_t - M‖²_max ≺ max_{a,b} 𝓛^{(2)}`;
the RBM2D forms split it into the diagonal entries (`GiiOmegaSeq`) and the off-diagonal entries
(`GijOmegaSeq`, right side `gexRHS`).  On `Ω` the loop floor `W^{-d} ≤ 4 max 𝓛` (`W^{-c} ≤ 1/2`,
eventually) absorbs the term `W^{-d}` of `gexRHS`, the ball count `|{a' : |a'-a| ≤ 1}| ≤ 3^d`
gives `gexRHS ≤ (9^d + 4) max 𝓛`, and the constant is absorbed in `N^{τ/2}`.  Needs `N → ∞`,
`W → ∞` (`Admissible`) and `|E| ≤ 2`. -/
theorem stGiiGEX_of_omegaSeq {E t : ℕ → ℝ} {c 𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡)
    (hE : ∀ n, |E n| ≤ 2) (hc : 0 < c)
    (hii : GiiOmegaSeq sz E t c) (hij : GijOmegaSeq sz E t c) : STGiiGEX sz E t c := by
  have hsize : Tendsto sz.size atTop atTop := sz.tendsto_size hA.2.2.1
  have h1 : StochDomAt sz.seqP sz.size (U := fun n => Idx d (sz.L n) (sz.W n))
      (fun n x ω => omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
        diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) x)
      (fun n _ ω => maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)) := by
    have h := perTimeDomAt_mono (fun n (x : Idx d (sz.L n) (sz.W n)) => ((), x)) hii
      (Eventually.of_forall fun n v ω => le_rfl) (Eventually.of_forall fun n v ω => le_rfl)
    exact Path.stochDomAt_of_perTimeDomAt sz.seqP sz.size (C := 1) (by norm_num)
      (Eventually.of_forall fun n => card_Idx_le sz n) h
  have h2 : StochDomAt sz.seqP sz.size
      (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
        offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.1 p.2)
      (fun n p ω => gexRHS d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)
        (STblk sz n p.2) (STblk sz n p.1)) := by
    have h := perTimeDomAt_mono
      (fun n (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) => ((), p)) hij
      (Eventually.of_forall fun n v ω => le_rfl) (Eventually.of_forall fun n v ω => le_rfl)
    exact Path.stochDomAt_of_perTimeDomAt sz.seqP sz.size (C := 2) (by norm_num)
      (Eventually.of_forall fun n => card_Idx_prod_le sz n) h
  unfold STGiiGEX Prec
  refine StochDomAt.of_subset_union hsize h1 h2 ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [eventually_W_rpow_neg_le sz hA hc,
    hsize.eventually (eventually_le_rpow ((9 : ℝ) ^ d + 4) (half_pos hτ))] with n hWn hNn
  rintro ω ⟨p, hp⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  set m := maxLoopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) with hm
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (norm_loopPM_le_max _ _ _ 0 0)
  have hp' : N ^ τ * m <
      omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
        ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2 := by
    rw [omegaInd_eq, hm, ← stmaxLoop2_eq_maxLoopPM]; exact hp
  have hNτ : N ^ (τ / 2) ≤ N ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hNN : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hNh : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hN0.le _
  by_cases hcond : ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) i j ≤
        ((sz.W n : ℕ) : ℝ) ^ (-c)
  · have hind : omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) = 1 := by
      unfold omegaInd; exact ite_eq_left hcond
    rw [hind, one_mul] at hp'
    by_cases hxy : p.1 = p.2
    · refine Or.inl ⟨p.1, ?_⟩
      change N ^ (τ / 2) * m <
        omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
          diagSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.1
      rw [hind, one_mul, diagSq_eq]
      have hsq : ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2 =
          ‖STGM sz n (E n) (t n) ω p.1 p.1‖ ^ 2 := by rw [hxy]
      calc N ^ (τ / 2) * m ≤ N ^ τ * m := mul_le_mul_of_nonneg_right hNτ hm0
        _ < ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2 := hp'
        _ = ‖STGM sz n (E n) (t n) ω p.1 p.1‖ ^ 2 := hsq
    · refine Or.inr ⟨p, ?_⟩
      by_contra hnot
      have hnot' : omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) *
          offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.1 p.2 ≤
          N ^ (τ / 2) * gexRHS d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)
            (STblk sz n p.2) (STblk sz n p.1) := not_lt.mp hnot
      rw [hind, one_mul] at hnot'
      have hoff : offSq d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.1 p.2 =
          ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2 := by
        rw [stGM_ne sz n _ _ ω hxy]
        unfold offSq
        rw [ite_eq_right hxy]
        rfl
      rw [hoff] at hnot'
      have hfloor := inv_W_pow_le_maxLoopPM (hE n) (sz.seqHflow_isHermitian n (t n) ω) hWn hcond
      have hg := gexRHS_le_ball (d := d) (L := sz.L n) (W := sz.W n) (E n) (t n)
        (sz.seqHflow n (t n) ω) (STblk sz n p.2) (STblk sz n p.1)
      have h3 : N ^ (τ / 2) * gexRHS d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω)
            (STblk sz n p.2) (STblk sz n p.1) ≤
          N ^ (τ / 2) * (((9 : ℝ) ^ d + 4) * m) :=
        mul_le_mul_of_nonneg_left (by linarith) hNh
      have h4 : N ^ (τ / 2) * (((9 : ℝ) ^ d + 4) * m) ≤ N ^ (τ / 2) * (N ^ (τ / 2) * m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hNn hm0) hNh
      have h5 : N ^ (τ / 2) * (N ^ (τ / 2) * m) = N ^ τ * m := by rw [← mul_assoc, hNN]
      linarith
  · exfalso
    have hind : omegaInd d (sz.L n) (sz.W n) (E n) (t n) c (sz.seqHflow n (t n) ω) = 0 := by
      unfold omegaInd; exact ite_eq_right hcond
    rw [hind, zero_mul] at hp'
    have : 0 ≤ N ^ τ * m := mul_nonneg (Real.rpow_nonneg hN0.le _) hm0
    linarith

/-- `⟨(G_t - m) E_a⟩ = 𝓛^{(1)}_{t,+,a} - m(E)` (`tr E_a = 1`). -/
private theorem avgErr_eq_loop (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (a : Zd d (sz.L n)) :
    avgErr d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) true a =
      Lloop sz n E u (fun _ : Fin 1 => true) (fun _ => a) ω - mE E := by
  unfold avgErr greenBlk Lloop loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, Matrix.one_mul,
    trace_Eblk]
  simp [mSigma]

/-- **Bridge `GavLDetSeq ⇔ ‖𝓛^{(1)} - m‖ ≺ Ψ²`** (`(GavLGEX)`, `3_5:33`; `⟨(G-m)E_a⟩ =
𝓛^{(1)}_{+,a} - m(E)`): the union over the `L^d ≤ N` blocks is absorbed. -/
theorem gavLDetSeq_iff_prec (E t Ψ : ℕ → ℝ) :
    GavLDetSeq sz E t Ψ ↔
      sz.Prec (U := fun n => Zd d (sz.L n))
        (fun n a ω => ‖Lloop sz n (E n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (E n)‖)
        (fun n _ _ => Ψ n ^ 2) := by
  constructor
  · intro h
    have h1 : sz.PrecPT (U := fun n => Zd d (sz.L n))
        (fun n a ω => ‖Lloop sz n (E n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (E n)‖)
        (fun n _ _ => Ψ n ^ 2) :=
      perTimeDomAt_mono (fun n (a : Zd d (sz.L n)) => ((), a)) h
        (Eventually.of_forall fun n v ω => le_of_eq (by rw [avgErr_eq_loop]))
        (Eventually.of_forall fun n v ω => le_rfl)
    refine Path.stochDomAt_of_perTimeDomAt sz.seqP sz.size (C := 1) (by norm_num)
      (Eventually.of_forall fun n => ?_) h1
    rw [Real.rpow_one]
    exact_mod_cast card_Zd_le_size sz n
  · intro h
    exact perTimeDomAt_mono (fun n (p : Unit × Zd d (sz.L n)) => p.2)
      (perTimeDomAt_of_stochDomAt h)
      (Eventually.of_forall fun n v ω => le_of_eq (by rw [avgErr_eq_loop]))
      (Eventually.of_forall fun n v ω => le_rfl)

/-- **Bridge `max 𝓛 ≺ Ψ² ⇒ LoopDetSeq`** (`(initialGT2)`, `3_5:30`): each `|𝓛_{(+,-),(a,b)}|`
is at most `max_{a,b} 𝓛^{(2)}_{(-,+),(a,b)}` (`|𝓛_{(+,-),(a,b)}| = |𝓛_{(-,+),(b,a)}|`). -/
theorem loopDetSeq_of_prec {E t Ψ : ℕ → ℝ}
    (h : sz.Prec (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
      (fun n _ _ => Ψ n ^ 2)) : LoopDetSeq sz E t Ψ := by
  refine perTimeDomAt_mono (fun n (p : Unit × Zd d (sz.L n) × Zd d (sz.L n)) => p.1)
    (perTimeDomAt_of_stochDomAt h) (Eventually.of_forall fun n v ω => ?_)
    (Eventually.of_forall fun n v ω => le_rfl)
  rw [stmaxLoop2_eq_maxLoopPM]
  exact norm_loopPM_le_max _ _ _ _ _

/-- **Bridge `LoopDetSeq ⇒ max 𝓛 ≺ Ψ²`** (converse of `loopDetSeq_of_prec`): the union over the
`L^{2d} ≤ N²` pairs `(a,b)` is absorbed, and `max_{a,b} |𝓛_{(-,+),(a,b)}|` is attained at one pair. -/
theorem prec_maxLoop2_of_loopDetSeq {E t Ψ : ℕ → ℝ} (h : LoopDetSeq sz E t Ψ) :
    sz.Prec (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
      (fun n _ _ => Ψ n ^ 2) := by
  have hP : StochDomAt sz.seqP sz.size (U := fun n => Unit × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖loopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.2.1 p.2.2‖)
      (fun n _ _ => Ψ n ^ 2) := by
    refine Path.stochDomAt_of_perTimeDomAt sz.seqP sz.size (C := 2) (by norm_num)
      (Eventually.of_forall fun n => ?_) h
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_unit, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_one, one_mul, Real.rpow_two]
    have h1 : ((Fintype.card (Zd d (sz.L n)) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
      exact_mod_cast card_Zd_le_size sz n
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (Zd d (sz.L n)))]
  intro τ hτ D hD
  filter_upwards [hP τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨v, hv⟩
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup'
    (⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Zd d (sz.L n) × Zd d (sz.L n))).Nonempty)
    (fun p : Zd d (sz.L n) × Zd d (sz.L n) =>
      ‖loopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) p.1 p.2‖)
  refine ⟨((), q), ?_⟩
  have hv' : ((sz.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 <
      STmaxLoop2 sz n (E n) (t n) ω := hv
  rw [stmaxLoop2_eq_maxLoopPM] at hv'
  change ((sz.size n : ℕ) : ℝ) ^ τ * Ψ n ^ 2 <
    ‖loopPM d (sz.L n) (sz.W n) (E n) (t n) (sz.seqHflow n (t n) ω) q.1 q.2‖
  rw [← hq]
  exact hv'

/-- **The flow parametrization** (replaces RBM2D `v3_premises_of_mainIndHyp`,
`Green/Pins.lean:293`, on `STFlow` in place of `MainIndHyp`): at the energy `E = lemE z` of
`zztE` (`1_2:787`) and a time `t ≤ t₀ = lemT z`, `z_n ∈ 𝐃_{κ,ε}` gives the premises of
`GbEXPHypV3` with `κ/2` and `δ = ε/2`: `|E_n| ≤ |Re z_n| ≤ 2 - κ`, `t_n < 1`, and
`1 - t_n ≥ 1 - t₀ ≥ Im z_n / 4 ≥ N^{-1+ε}/4 ≥ N^{-1+ε/2}` eventually
((2.37), `lemma28_quant`: `t₀ ≥ 1/16`, `(1 - t₀) Im m(E) = √t₀ Im z`). -/
theorem v3_premises_of_stFlow {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (h : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (h1 : ∀ n, t n ≤ lemT (z n)) :
    sz.Admissible 𝔠 𝔡 ∧ (∀ n, |STflowE z n| < 2 - κ / 2) ∧ (∀ n, t n < 1) ∧
      sz.RangeCond (ε / 2) t := by
  obtain ⟨hA, hD⟩ := h
  have hN0 : ∀ n, (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := fun n => by
    exact_mod_cast sz.one_le_size n
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (hN0 n) _) (hD n).2.1
  refine ⟨hA, fun n => ?_, fun n => (h1 n).trans_lt (lemT_lt_one (him n)), ?_⟩
  · have h2 := (abs_lemE_le (him n)).trans (hD n).1
    change |lemE (z n)| < 2 - κ / 2
    linarith
  · have hN := sz.tendsto_size hA.2.2.1
    filter_upwards [hN.eventually (eventually_le_rpow 4 (half_pos hε))] with n hn
    have hz := him n
    obtain ⟨-, hq2, -, -⟩ := lemma28_quant (z := z n) hκ hz (hD n).2.2 (hD n).1
    have hmeq : (1 - lemT (z n)) * (mE (lemE (z n))).im =
        Real.sqrt (lemT (z n)) * (z n).im := by
      rw [← zt_im, zt_im_lemma28 hz]
    have hm1 : (mE (lemE (z n))).im ≤ 1 := by
      rw [mE_im]
      have : Real.sqrt (4 - lemE (z n) ^ 2) ≤ 2 :=
        Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg (lemE (z n))]⟩
      linarith
    have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT (z n)) :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
    have hlt : 0 < 1 - lemT (z n) := by linarith [lemT_lt_one hz]
    have h3 : (1 / 4) * (z n).im ≤ 1 - lemT (z n) := by
      have h4 : (1 - lemT (z n)) * (mE (lemE (z n))).im ≤ (1 - lemT (z n)) * 1 :=
        mul_le_mul_of_nonneg_left hm1 hlt.le
      nlinarith [mul_le_mul_of_nonneg_right hs4 hz.le]
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hNpos : 0 < N := hN0 n
    have hsplit : N ^ (-1 + ε) = N ^ (-1 + ε / 2) * N ^ (ε / 2) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    have hpos : 0 ≤ N ^ (-1 + ε / 2) := Real.rpow_nonneg hNpos.le _
    have h5 : N ^ (-1 + ε / 2) * 4 ≤ N ^ (-1 + ε) := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_left hn hpos
    have h6 := (hD n).2.1
    change N ^ (-1 + ε / 2) ≤ 1 - t n
    linarith [h1 n]

/-- **Bridge `GbEXPHypV3` (third clause) ⇒ `STGavLGEX`** (`(GavLGEX)`, `3_5:33`, under
`(initialGT2)`, `3_5:30`).  The ST pin carries the window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` of the paper
(RBM2D: `0 ≤ Ψ ≤ N^{-a}`): `a = 𝔠 ε₀` (`W ≥ N^𝔠`), `Ψ` is replaced by `max Ψ 0` (equal to `Ψ`
eventually) for the pointwise `0 ≤ Ψ` of the RBM2D clause, `(asGMc)` and `LoopDetSeq` are the
two `Prec` premises of `(initialGT2)` (`asGMcSeq_iff_prec`, `loopDetSeq_of_prec`), and the
conclusion `GavLDetSeq` is the ST conclusion (`gavLDetSeq_iff_prec`). -/
theorem stGavLGEX_of_v3 {κ 𝔠 𝔡 δ : ℝ} (hV3 : GbEXPHypV3 sz κ 𝔠 𝔡 δ) (hA : sz.Admissible 𝔠 𝔡)
    {E t : ℕ → ℝ} (hE : ∀ n, |E n| < 2 - κ) (h0 : ∀ n, 0 ≤ t n) (h1 : ∀ n, t n < 1)
    (hR : sz.RangeCond δ t) {ε₀ : ℝ} (hε₀ : 0 < ε₀) : STGavLGEX sz E t ε₀ := by
  intro Ψ hΨ1 hΨ2 hG hL
  have hAs : AsGMcSeq sz E t ε₀ := (asGMcSeq_iff_prec sz E t ε₀).2 hG
  have hv := (hV3 hA E t hE h0 h1 hR ε₀ hε₀).2.2 hAs
  -- the nonnegative control `Ψ' = max Ψ 0`
  have hpos : ∀ᶠ n in atTop, 0 ≤ Ψ n := hΨ1.mono fun n hn =>
    le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hn
  have hΨ'0 : ∀ n, 0 ≤ max (Ψ n) 0 := fun n => le_max_right _ _
  have heq : ∀ᶠ n in atTop, max (Ψ n) 0 = Ψ n := hpos.mono fun n hn => max_eq_left hn
  have hΨ'a : ∀ᶠ n : ℕ in atTop,
      max (Ψ n) 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * ε₀)) := by
    filter_upwards [hΨ2, hA.2.2.2.1] with n hn hB
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hW : ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(𝔠 * ε₀)) := by
      have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 𝔠) hB (by linarith :
        -ε₀ ≤ 0)
      rwa [← Real.rpow_mul hN0.le, show 𝔠 * -ε₀ = -(𝔠 * ε₀) by ring] at h
    exact max_le (hn.trans hW) (Real.rpow_nonneg hN0.le _)
  have hL' : sz.Prec (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
      (fun n _ _ => max (Ψ n) 0 ^ 2) :=
    stochDomAt_mono (fun n (v : Unit) => v) hL (Eventually.of_forall fun n v ω => le_rfl)
      (heq.mono fun n hn v ω => by rw [hn])
  have hLoop : LoopDetSeq sz E t (fun n => max (Ψ n) 0) := loopDetSeq_of_prec sz hL'
  have hGav := hv.2.2 (fun n => max (Ψ n) 0) (𝔠 * ε₀) (mul_pos hA.1 hε₀) hΨ'0 hΨ'a hLoop
  have hP := (gavLDetSeq_iff_prec sz E t (fun n => max (Ψ n) 0)).1 hGav
  exact stochDomAt_mono (fun n (a : Zd d (sz.L n)) => a) hP (Eventually.of_forall fun n v ω => le_rfl)
    (heq.mono fun n hn v ω => by rw [hn])

/-- `GbEXPV3Theorem ⇒ STGbEXPii`: `(GiiGEX)` for the flow, every `ε₀ > 0`, every `t ∈ [0, t₀]`. -/
theorem stGbEXPii_of_v3 (h : GbEXPV3Theorem d) : STGbEXPii d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t h0 h1 ε₀ hε₀
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz hκ hε hflow h1
  have hV := h sz (κ / 2) 𝔠 𝔡 (ε / 2) (by positivity) hA.1 h𝔡 (by positivity)
  have hc := hV hA (STflowE z) t hE h0 ht1 hR ε₀ hε₀
  exact stGiiGEX_of_omegaSeq sz hA (fun n => by linarith [hE n]) hε₀ hc.2.1 hc.1

/-- `GbEXPV3Theorem ⇒ STGbEXPij`: `(GijGEX)` for the flow. -/
theorem stGbEXPij_of_v3 (h : GbEXPV3Theorem d) : STGbEXPij d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t h0 h1 ε₀ hε₀
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz hκ hε hflow h1
  have hV := h sz (κ / 2) 𝔠 𝔡 (ε / 2) (by positivity) hA.1 h𝔡 (by positivity)
  exact stGijGEX_of_gijOmegaSeq sz (hV hA (STflowE z) t hE h0 ht1 hR ε₀ hε₀).1

/-- `GbEXPV3Theorem ⇒ STGbEXPav`: `(GavLGEX)` for the flow. -/
theorem stGbEXPav_of_v3 (h : GbEXPV3Theorem d) : STGbEXPav d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t h0 h1 ε₀ hε₀
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz hκ hε hflow h1
  have hV := h sz (κ / 2) 𝔠 𝔡 (ε / 2) (by positivity) hA.1 h𝔡 (by positivity)
  exact stGavLGEX_of_v3 sz hV hA hE h0 ht1 hR hε₀

/-- **`GbEXPV3Theorem ⇒ STGbEXP`**: the three parts of `lem_GbEXP` (`3_5:14-40`) in the ST form
follow from the RBM2D form of the pin. -/
theorem stGbEXP_of_v3 (h : GbEXPV3Theorem d) : STGbEXP d :=
  ⟨stGbEXPii_of_v3 h, stGbEXPij_of_v3 h, stGbEXPav_of_v3 h⟩

end Bridge

/-! ## 8. Extreme-input checks (RBM2D `Green/Pins.lean` section 5, H26) -/

section Extreme

/-- A per-time domination whose left side is `≤ 0` and right side `≥ 0` holds.  RBM2D
`Green/Pins.lean:308`. -/
theorem perTimeDomAt_of_nonpos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (size : ℕ → ℕ) {U : ℕ → Type*} (ξ ζ : ∀ l, U l → Ω → ℝ)
    (hξ : ∀ l u ω, ξ l u ω ≤ 0) (hζ : ∀ l u ω, 0 ≤ ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ _ D _
  refine Eventually.of_forall fun l u => ?_
  have hempty : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (hξ l u ω).trans
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) τ) (hζ l u ω))
  rw [hempty, measure_empty]
  exact bot_le

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `G_0(+) = m I` at `H = 0`, `u = 0` (`z_0 = E + m`, `m (m + E) = -1`): the identity inside
`Gauss.Sizes.Lloop_zero_one`, for any finite index. -/
private theorem gres_zero_true {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ℝ} (hE : |E| ≤ 2) :
    Gres (0 : Matrix ι ι ℂ) (zt E 0) true = mE E • (1 : Matrix ι ι ℂ) := by
  have hm := mE_mul hE
  have hzt : zt E 0 = (E : ℂ) + mE E := by simp [zt]
  have hmz : (-((E : ℂ) + mE E))⁻¹ = mE E := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-1 : ℂ) * hm
  have hne : (E : ℂ) + mE E ≠ 0 := by
    intro h0
    rw [add_comm, h0, mul_zero] at hm
    norm_num at hm
  rw [Gres]
  simp only [↓reduceIte]
  rw [hzt, zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hne), hmz]

/-- At `u = 0` and `M = 0` (`H_0 = 0`): `G_0 = m · 1`.  RBM2D `Green/Pins.lean:325`. -/
theorem greenBlk_time_zero {E : ℝ} (hE : |E| ≤ 2) :
    greenBlk d L W E 0 0 true = mE E • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
  unfold greenBlk
  rw [blockMat_zero, gres_zero_true hE]

theorem gexRHS_nonneg (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) :
    0 ≤ gexRHS d L W E u M a b := by
  unfold gexRHS
  refine add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_) ?_
  · split_ifs <;> simp
  · split_ifs <;> positivity

theorem maxLoopPM_nonneg (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    0 ≤ maxLoopPM d L W E u M :=
  (norm_nonneg _).trans (norm_loopPM_le_max E u M 0 0)

/-- **Reading of the swapped pin.**  `gexRHS … b a` is the display of (`GijGEX`), `3_5:24`, at
blocks `(a,b)` with `𝓛_{(+,-),(a',b')}` replaced by `𝓛_{(+,-),(b',a')}` (RBM2D T2066a).  RBM2D
`Green/Pins.lean:366`. -/
theorem gexRHS_swap_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) :
    gexRHS d L W E u M b a =
      (∑ a' : Zd d L, ∑ b' : Zd d L,
        if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
          ‖loopPM d L W E u M b' a'‖ else 0) +
      if zdistInf d L (a - b) ≤ 1 then ((W : ℝ) ^ d)⁻¹ else 0 := by
  unfold gexRHS
  rw [Finset.sum_comm, ← neg_sub a b, zdistInf_neg]
  congr 1
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
  simp only [and_comm]

theorem offSq_time_zero {E : ℝ} (hE : |E| ≤ 2) (p q : Idx d L W) :
    offSq d L W E 0 0 p q = 0 := by
  unfold offSq
  split_ifs with h
  · rfl
  · rw [gres_zero_true hE]
    simp [Matrix.smul_apply, Matrix.one_apply_ne h]

theorem diagSq_time_zero {E : ℝ} (hE : |E| ≤ 2) (p : Idx d L W) :
    diagSq d L W E 0 0 p = 0 := by
  unfold diagSq
  rw [gres_zero_true hE]
  simp

theorem llErrMat_time_zero {E : ℝ} (hE : |E| ≤ 2) (i j : Idx d L W) :
    llErrMat d L W E 0 0 i j = 0 := by
  unfold llErrMat
  rw [gres_zero_true hE]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.smul_apply, Matrix.one_apply_ne h, h]

theorem avgErr_time_zero {E : ℝ} (hE : |E| ≤ 2) (a : Zd d L) :
    avgErr d L W E 0 0 true a = 0 := by
  unfold avgErr
  rw [greenBlk_time_zero hE]
  simp [mSigma]

/-- **H26, the diagonal at `t = 0`**: `|G_{pp}|² = |m|² = 1` (why `offSq` excludes `p = q`).
RBM2D `Green/Pins.lean:398`. -/
theorem diag_entry_sq_time_zero {E : ℝ} (hE : |E| ≤ 2) (p : Vtx d L W) :
    ‖greenBlk d L W E 0 0 true p p‖ ^ 2 = 1 := by
  rw [greenBlk_time_zero hE]
  simp [norm_mE hE]

omit [NeZero W] in
/-- `Σ_{v : Vtx} (if v.1 = b then F v else 0) = Σ_β F (b, β)`. -/
private theorem sum_vtx_ite (F : Vtx d L W → ℝ) (b : Zd d L) :
    ∑ v : Vtx d L W, (if v.1 = b then F v else 0) = ∑ β : Fin (W ^ d), F (b, β) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp
  · intro x _ hx
    simp [hx]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-- **`|𝓛_{(+,-),(a,b)}|` in the entries of the block resolvent** (RBM2D `norm_loopPM_eq`,
`Green/Pins.lean:406`, with `W^{-2}` ↦ `W^{-d}` and the `W^d`-point blocks): for Hermitian `M`,
`|𝓛_{u,(+,-),(a,b)}| = (W^{-d})² Σ_{β,α} |G_{(b,β),(a,α)}|²`: rows in block `b`, columns in
block `a`. -/
theorem norm_loopPM_eq {E u : ℝ} (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian)
    (a b : Zd d L) :
    ‖loopPM d L W E u M a b‖ = (((W : ℝ)⁻¹ ^ d) ^ 2) *
      ∑ β : Fin (W ^ d), ∑ α : Fin (W ^ d), ‖greenBlk d L W E u M true (b, β) (a, α)‖ ^ 2 := by
  unfold loopPM
  rw [loopFine_pm_formula_vtx M hM (zt E u) a b, Complex.norm_real, Real.norm_of_nonneg
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => by
      split_ifs <;> positivity))]
  have h1 : ∀ v : Vtx d L W, (∑ w : Vtx d L W, if v.1 = b ∧ w.1 = a then
      ‖Gres (blockMat d L W M) (zt E u) true v w‖ ^ 2 else 0) =
      if v.1 = b then ∑ w : Vtx d L W, (if w.1 = a then
        ‖Gres (blockMat d L W M) (zt E u) true v w‖ ^ 2 else 0) else 0 := fun v => by
    by_cases hv : v.1 = b <;> simp [hv]
  have hsum : (∑ v : Vtx d L W, ∑ w : Vtx d L W, if v.1 = b ∧ w.1 = a then
      ‖Gres (blockMat d L W M) (zt E u) true v w‖ ^ 2 else 0) =
      ∑ β : Fin (W ^ d), ∑ α : Fin (W ^ d),
        ‖greenBlk d L W E u M true (b, β) (a, α)‖ ^ 2 := by
    simp only [h1]
    rw [sum_vtx_ite (fun v => ∑ w : Vtx d L W, (if w.1 = a then
      ‖Gres (blockMat d L W M) (zt E u) true v w‖ ^ 2 else 0)) b]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [sum_vtx_ite (fun w => ‖Gres (blockMat d L W M) (zt E u) true (b, β) w‖ ^ 2) a]
    rfl
  rw [hsum, show ((W : ℝ)⁻¹ ^ d) = ((W : ℝ) ^ d)⁻¹ from inv_pow _ _]

private theorem zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

/-- `|𝓛_{(+,-),(a,b)}|` is one of the terms of `gexRHS … a b` (`a' = a`, `b' = b`). -/
private theorem norm_loopPM_le_gexRHS (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a b : Zd d L) : ‖loopPM d L W E u M a b‖ ≤ gexRHS d L W E u M a b := by
  unfold gexRHS
  have h0 : 0 ≤ (if zdistInf d L (a - b) ≤ 1 then ((W : ℝ) ^ d)⁻¹ else 0) := by
    split_ifs <;> positivity
  have hnn : ∀ (x y : Zd d L), 0 ≤ (if zdistInf d L (x - a) ≤ 1 ∧ zdistInf d L (y - b) ≤ 1 then
      ‖loopPM d L W E u M x y‖ else 0) := fun x y => by split_ifs <;> positivity
  have h1 : ‖loopPM d L W E u M a b‖ ≤ ∑ a' : Zd d L, ∑ b' : Zd d L,
      if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
        ‖loopPM d L W E u M a' b'‖ else 0 := by
    calc ‖loopPM d L W E u M a b‖
        = (if zdistInf d L (a - a) ≤ 1 ∧ zdistInf d L (b - b) ≤ 1 then
            ‖loopPM d L W E u M a b‖ else 0) := by
          simp [zdistInf_zero]
      _ ≤ ∑ b' : Zd d L, (if zdistInf d L (a - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
            ‖loopPM d L W E u M a b'‖ else 0) :=
          Finset.single_le_sum (f := fun b' : Zd d L =>
            if zdistInf d L (a - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
              ‖loopPM d L W E u M a b'‖ else 0) (fun y _ => hnn a y) (Finset.mem_univ b)
      _ ≤ _ := Finset.single_le_sum (f := fun a' : Zd d L => ∑ b' : Zd d L,
            if zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1 then
              ‖loopPM d L W E u M a' b'‖ else 0)
          (fun x _ => Finset.sum_nonneg fun y _ => hnn x y) (Finset.mem_univ a)
  linarith

/-- **H26, `W = 1`** (orientation, RBM2D T2066a): for Hermitian `M`, the swapped right side
`gexRHS … [q] [p]` contains the term `𝓛_{(+,-),([q],[p])} = |G_{pq}|²` itself, so the
off-diagonal left side is bounded by it pointwise.  RBM2D `Green/Pins.lean:425`. -/
theorem offSq_le_gexRHS_swap_W1 {E u : ℝ} (M : Matrix (Idx d L 1) (Idx d L 1) ℂ)
    (hM : M.IsHermitian) (p q : Idx d L 1) :
    offSq d L 1 E u M p q ≤ gexRHS d L 1 E u M (split d L 1 q).1 (split d L 1 p).1 := by
  unfold offSq
  split_ifs with hpq
  · exact gexRHS_nonneg _ _ _ _ _
  · refine le_trans ?_ (norm_loopPM_le_gexRHS E u M _ _)
    unfold loopPM
    rw [loopFine_pm_formula M hM (zt E u), Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun x _ => by
        split_ifs <;> positivity))]
    simp only [Nat.cast_one, one_pow, inv_one]
    calc ‖Gres M (zt E u) true p q‖ ^ 2
        = (if (split d L 1 p).1 = (split d L 1 p).1 ∧ (split d L 1 q).1 = (split d L 1 q).1 then
            ‖Gres M (zt E u) true p q‖ ^ 2 else 0) := by simp
      _ ≤ ∑ x : Idx d L 1, (if (split d L 1 p).1 = (split d L 1 p).1 ∧
            (split d L 1 x).1 = (split d L 1 q).1 then ‖Gres M (zt E u) true p x‖ ^ 2 else 0) :=
          Finset.single_le_sum (f := fun x : Idx d L 1 =>
            if (split d L 1 p).1 = (split d L 1 p).1 ∧ (split d L 1 x).1 = (split d L 1 q).1 then
              ‖Gres M (zt E u) true p x‖ ^ 2 else 0)
            (fun x _ => by split_ifs <;> positivity) (Finset.mem_univ q)
      _ ≤ _ := by
          have := Finset.single_le_sum (f := fun y : Idx d L 1 => ∑ x : Idx d L 1,
            if (split d L 1 y).1 = (split d L 1 p).1 ∧ (split d L 1 x).1 = (split d L 1 q).1 then
              ‖Gres M (zt E u) true y x‖ ^ 2 else 0)
            (fun y _ => Finset.sum_nonneg fun x _ => by split_ifs <;> positivity)
            (Finset.mem_univ p)
          simpa using this

end Extreme

section TimeZero

variable {d : ℕ} (sz : Sizes d)

private theorem seqHflow_zero' (n : ℕ) (ω : sz.SeqΩ) : sz.seqHflow n 0 ω = 0 := by
  simp [seqHflow]

/-- **H26, `t ≡ 0`**: every conclusion of `GbEXPHypV3` (and `GavLGEXRandHyp`) holds at the time
sequence `t ≡ 0`, for every bulk energy sequence, every `c` and every `Ψ`.  RBM2D
`Green/Pins.lean:463`. -/
theorem conclusions_time_zero {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2) (c : ℝ) (Ψ : ℕ → ℝ) :
    GijOmegaSeq sz E (fun _ => 0) c ∧ GiiOmegaSeq sz E (fun _ => 0) c ∧
      GijSeq sz E (fun _ => 0) ∧ GiiSeq sz E (fun _ => 0) ∧
      GavLDetSeq sz E (fun _ => 0) Ψ ∧ GavLRandSeq sz E (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_)
      (fun n p ω => gexRHS_nonneg _ _ _ _ _)
    simp only [seqHflow_zero', offSq_time_zero (hE n), mul_zero, le_refl]
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_)
      (fun n p ω => maxLoopPM_nonneg _ _ _)
    simp only [seqHflow_zero', diagSq_time_zero (hE n), mul_zero, le_refl]
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_)
      (fun n p ω => gexRHS_nonneg _ _ _ _ _)
    simp only [seqHflow_zero', offSq_time_zero (hE n), le_refl]
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_)
      (fun n p ω => maxLoopPM_nonneg _ _ _)
    simp only [seqHflow_zero', diagSq_time_zero (hE n), le_refl]
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_) (fun n p ω => sq_nonneg _)
    simp only [seqHflow_zero', avgErr_time_zero (hE n), norm_zero, le_refl]
  · refine perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_)
      (fun n p ω => maxLoopPM_nonneg _ _ _)
    simp only [seqHflow_zero', avgErr_time_zero (hE n), norm_zero, le_refl]

/-- (`asGMc`) holds at `t ≡ 0` (`G_0 = m I`, so `‖G_0 - m‖_max = 0`). -/
theorem asGMcSeq_time_zero {E : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2) (c : ℝ) :
    AsGMcSeq sz E (fun _ => 0) c := by
  refine perTimeDomAt_of_nonpos _ _ _ _ (fun n p ω => ?_)
    (fun n p ω => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  simp only [seqHflow_zero', llErrMat_time_zero (hE n), le_refl]

end TimeZero

/-! ## 9. Compiled nonempty instances at `d = 3`

The data are those of `RBM3D/Induction/Defs.lean`, section 3: the merged preflight sequence
`sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`; `n = 0`:
`L = 4`, `W = 32`, `N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; the flow points
`z_n = 1/2 + i N_n^{-4/5} ∈ 𝐃_{κ,ε}`, `κ = ε = 1/10`, the energy `E_n = lemE z_n`, `s ≡ 0`,
`t ≡ 1/16 ≤ t₀`.  What stays a hypothesis of an instance is the statement of another pin (the
RBM2D forms `GbEXPHypV3`, `GbEXPV3Theorem`, the ST pins) or a stochastic premise of the theorem
itself; every deterministic hypothesis is discharged. -/

namespace Instance

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- **The deterministic premises of `GbEXPHypV3`** at `(sz0, lemE ∘ z0, t ≡ 1/16)` with
`κ = (1/10)/2`, `𝔠 = 1/6`, `𝔡 = 1/10`, `δ = (1/10)/2`, all at once, from the flow `STFlow` of the
section-3 data (`v3_premises_of_stFlow`). -/
theorem premises :
    sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, |STflowE z0 n| < 2 - (1 / 10) / 2) ∧
      (∀ n, 0 ≤ tInst n) ∧ (∀ n, tInst n < 1) ∧ sz0.RangeCond ((1 / 10) / 2) tInst := by
  obtain ⟨hA, hE, ht1, hR⟩ := v3_premises_of_stFlow sz0 (by norm_num) (by norm_num) flow_z0
    (t := tInst) (fun n => by
      simp only [tInst]
      exact (by norm_num : (1 / 16 : ℝ) ≤ 1 / 16).trans (sixteenth_le_lemT n))
  exact ⟨hA, hE, fun n => by simp [tInst], ht1, hR⟩

/-- `RangeCond` at an earlier time sequence (`rangeCond_mono`): `u ≡ 0 ≤ t ≡ 1/16`. -/
theorem rangeCond_sInst : sz0.RangeCond ((1 / 10) / 2) sInst :=
  rangeCond_mono sz0 premises.2.2.2.2 (fun n => by simp only [sInst, tInst]; norm_num)

/-- **`gijGEXPTSwap_giiGEXPT_of_V3`, instantiated** at `s ≡ 0`, `t ≡ 1/16`, `c = 1/40`: the pin
`GbEXPHypV3` and the per-time (`asGMc`) stay hypotheses; `Admissible`, the bulk, the time and range
conditions are discharged. -/
theorem inst_gijGEXPTSwap
    (hV3 : GbEXPHypV3 sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2))
    (hAs : AsGMcPT sz0 (STflowE z0) sInst tInst (1 / 40)) :
    GijGEXPTSwap sz0 (STflowE z0) sInst tInst ∧ GiiGEXPT sz0 (STflowE z0) sInst tInst :=
  gijGEXPTSwap_giiGEXPT_of_V3 sz0 hV3 premises.1 premises.2.1 (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) premises.2.2.2.1 premises.2.2.2.2
    (by norm_num) hAs

/-- **`perTime_timeIcc_of_forall_seq`, instantiated with no stochastic premise**: the envelope
`|𝓛^{(1)}_{u,+,a}| ≤ η_u⁻¹` (`Sizes.norm_Lloop_le`) holds per time at every time sequence in
`[0, 1/16]` (deterministic domination), hence per time over `TimeIcc 0 (1/16)`. -/
theorem inst_perTime_timeIcc :
    PerTimeDomAt sz0.seqP sz0.size (U := fun n => TimeIcc sInst tInst n × Zd 3 (sz0.L n))
      (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) p.1 (fun _ : Fin 1 => true) (fun _ => p.2) ω‖)
      (fun n p _ => (etaT (STflowE z0 n) p.1)⁻¹) := by
  have hE : ∀ n, |STflowE z0 n| < 2 := fun n => abs_lemE_lt_two (z0_im_pos n)
  refine perTime_timeIcc_of_forall_seq sz0.seqP sz0.size (fun n => by simp [sInst, tInst])
    (fun n => ⟨0⟩)
    (fun n u a ω => ‖Lloop sz0 n (STflowE z0 n) u (fun _ : Fin 1 => true) (fun _ => a) ω‖)
    (fun n u a ω => (etaT (STflowE z0 n) u)⁻¹) ?_
  intro u hu
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hu n).2 (by simp only [tInst]; norm_num)
  refine precPT_of_le sz0 (fun n _ ω => ?_) (fun n p ω => ?_)
  · exact inv_nonneg.mpr (etaT_pos (hE n) (hu1 n)).le
  · have := Sizes.norm_Lloop_le sz0 n (hE n) (hu1 n) (k := 0) (fun _ => true) (fun _ => p.2) ω
    simpa using this

/-- **`perSeq_of_perTime_timeIcc`, instantiated** at the section `u ≡ 1/16`: the per-time bound of
`inst_perTime_timeIcc` at the single time sequence `1/16`. -/
theorem inst_perSeq :
    PerTimeDomAt sz0.seqP sz0.size (U := fun n => Unit × Zd 3 (sz0.L n))
      (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (tInst n) (fun _ : Fin 1 => true)
        (fun _ => p.2) ω‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹) :=
  perSeq_of_perTime_timeIcc sz0.seqP sz0.size (V := fun n => Zd 3 (sz0.L n)) (fun n => ⟨0⟩)
    (fun n u a ω => ‖Lloop sz0 n (STflowE z0 n) u (fun _ : Fin 1 => true) (fun _ => a) ω‖)
    (fun n u a ω => (etaT (STflowE z0 n) u)⁻¹) inst_perTime_timeIcc tInst
    (fun n => ⟨by simp [sInst, tInst], le_rfl⟩)

/-- `asGMcSeq_iff_prec` at the section-3 data: `‖G_t - M‖_max ≺ W^{-ε₀}`, `ε₀ = 1/20`. -/
theorem inst_asGMcSeq_iff :
    AsGMcSeq sz0 (STflowE z0) tInst (1 / 20) ↔
      sz0.Prec (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n p ω => ‖STGM sz0 n (STflowE z0 n) (tInst n) ω p.1 p.2‖)
        (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ))) :=
  asGMcSeq_iff_prec sz0 (STflowE z0) tInst (1 / 20)

/-- **`stGijGEX_of_gijOmegaSeq`, instantiated**; the stochastic premise is the hypothesis. -/
theorem inst_stGijGEX (h : GijOmegaSeq sz0 (STflowE z0) tInst (1 / 20)) :
    STGijGEX sz0 (STflowE z0) tInst (1 / 20) :=
  stGijGEX_of_gijOmegaSeq sz0 h

/-- **`giiOmegaSeq_of_stGiiGEX`, instantiated.** -/
theorem inst_giiOmegaSeq (h : STGiiGEX sz0 (STflowE z0) tInst (1 / 20)) :
    GiiOmegaSeq sz0 (STflowE z0) tInst (1 / 20) :=
  giiOmegaSeq_of_stGiiGEX sz0 h

/-- **`stGiiGEX_of_omegaSeq`, instantiated**: `Admissible` (`N → ∞`, `W ≥ N^{1/6}`, `(eq:WO)`),
`|E_n| ≤ 2` and `c > 0` are discharged; the two RBM2D forms are the hypotheses. -/
theorem inst_stGiiGEX (hii : GiiOmegaSeq sz0 (STflowE z0) tInst (1 / 20))
    (hij : GijOmegaSeq sz0 (STflowE z0) tInst (1 / 20)) :
    STGiiGEX sz0 (STflowE z0) tInst (1 / 20) :=
  stGiiGEX_of_omegaSeq sz0 sz0_admissible (fun n => (abs_lemE_lt_two (z0_im_pos n)).le)
    (by norm_num) hii hij

/-- **`gavLDetSeq_iff_prec`, instantiated** at the deterministic control `Ψ_n = W_n^{-1}`. -/
theorem inst_gavLDetSeq_iff :
    GavLDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ↔
      sz0.Prec (U := fun n => Zd 3 (sz0.L n))
        (fun n a ω => ‖Lloop sz0 n (STflowE z0 n) (tInst n) (fun _ : Fin 1 => true) (fun _ => a) ω -
          mE (STflowE z0 n)‖)
        (fun n _ _ => (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2) :=
  gavLDetSeq_iff_prec sz0 (STflowE z0) tInst _

/-- **`loopDetSeq_of_prec`, instantiated** at `Ψ_n = W_n^{-1}`; the `Prec` premise of
`(initialGT2)` is the hypothesis. -/
theorem inst_loopDetSeq
    (h : sz0.Prec (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2 sz0 n (STflowE z0 n) (tInst n) ω)
      (fun n _ _ => (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2)) :
    LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  loopDetSeq_of_prec sz0 h

/-- The pin `GbEXPHypV3` at the section-3 data, from `GbEXPV3Theorem 3`. -/
theorem inst_hyp (h : GbEXPV3Theorem 3) :
    GbEXPHypV3 sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2) :=
  h sz0 _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **`stGavLGEX_of_v3`, instantiated**: the third clause of the RBM2D pin gives the ST form of
`(GavLGEX)` at `t ≡ 1/16`, `ε₀ = 1/20`. -/
theorem inst_stGavLGEX
    (hV3 : GbEXPHypV3 sz0 ((1 / 10) / 2) (1 / 6) (1 / 10) ((1 / 10) / 2)) :
    STGavLGEX sz0 (STflowE z0) tInst (1 / 20) :=
  stGavLGEX_of_v3 sz0 hV3 premises.1 premises.2.1 premises.2.2.1 premises.2.2.2.1
    premises.2.2.2.2 (by norm_num)

/-- **`stGbEXP_of_v3`, instantiated**: from the RBM2D pin `GbEXPV3Theorem 3`, the three parts of
`lem_GbEXP` in the ST form at the section-3 data. -/
theorem inst_stGbEXP_of_v3 (h : GbEXPV3Theorem 3) :
    STGiiGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tInst (1 / 20) :=
  inst_gbEXP (stGbEXP_of_v3 h)

/-- **`conclusions_time_zero`, instantiated** (no hypothesis): every conclusion of the pin holds
at `t ≡ 0` along the section-3 energy. -/
theorem inst_conclusions_time_zero (c : ℝ) (Ψ : ℕ → ℝ) :
    GijOmegaSeq sz0 (STflowE z0) (fun _ => 0) c ∧ GiiOmegaSeq sz0 (STflowE z0) (fun _ => 0) c ∧
      GijSeq sz0 (STflowE z0) (fun _ => 0) ∧ GiiSeq sz0 (STflowE z0) (fun _ => 0) ∧
      GavLDetSeq sz0 (STflowE z0) (fun _ => 0) Ψ ∧ GavLRandSeq sz0 (STflowE z0) (fun _ => 0) :=
  conclusions_time_zero sz0 (fun n => (abs_lemE_lt_two (z0_im_pos n)).le) c Ψ

/-- **`norm_loopPM_eq`, instantiated** at `n = 0` (`d = 3`, `L = 4`, `W = 32`): `|𝓛_{(+,-),(a,b)}| =
(W^{-3})² Σ_{β,α} |G_{(b,β),(a,α)}|²` for the Hermitian matrix `H_u` of the model at every
`u`, `ω`, `E`. -/
theorem inst_norm_loopPM_eq (E u : ℝ) (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :
    ‖loopPM 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) a b‖ =
      (((sz0.W 0 : ℕ) : ℝ)⁻¹ ^ 3) ^ 2 * ∑ β : Fin (sz0.W 0 ^ 3), ∑ α : Fin (sz0.W 0 ^ 3),
        ‖greenBlk 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) true (b, β) (a, α)‖ ^ 2 :=
  norm_loopPM_eq (sz0.seqHflow 0 u ω) (sz0.seqHflow_isHermitian 0 u ω) a b

/-- The extreme-input checks at `E = 1/2`, `L = 4`, `W = 32`, `d = 3`, `p ≠ q`: `G_0 = m I`, so
`offSq = diagSq = 0`, `⟨(G_0 - m) E_a⟩ = 0` and `|G_{pp}|² = 1`. -/
theorem inst_time_zero_checks :
    greenBlk 3 4 32 (1 / 2) 0 0 true = mE (1 / 2) • (1 : Matrix (Vtx 3 4 32) (Vtx 3 4 32) ℂ) ∧
      offSq 3 4 32 (1 / 2) 0 0 (0 : Idx 3 4 32) (Pi.single 0 1) = 0 ∧
      diagSq 3 4 32 (1 / 2) 0 0 (Pi.single 0 1 : Idx 3 4 32) = 0 ∧
      avgErr 3 4 32 (1 / 2) 0 0 true 0 = 0 ∧
      ‖greenBlk 3 4 32 (1 / 2) 0 0 true (0, ⟨0, by norm_num⟩) (0, ⟨0, by norm_num⟩)‖ ^ 2 = 1 := by
  have hE : |(1 / 2 : ℝ)| ≤ 2 := by rw [abs_of_pos (by norm_num)]; norm_num
  exact ⟨greenBlk_time_zero hE, offSq_time_zero hE _ _, diagSq_time_zero hE _,
    avgErr_time_zero hE _, diag_entry_sq_time_zero hE _⟩

/-- `gexRHS_nonneg`, `maxLoopPM_nonneg` and the swapped reading `gexRHS_swap_eq` at the model matrix
`H_u` of the section-3 data, `n = 0`. -/
theorem inst_gexRHS_checks (E u : ℝ) (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :
    0 ≤ gexRHS 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) a b ∧
      0 ≤ maxLoopPM 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) ∧
      gexRHS 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) b a =
        (∑ a' : Zd 3 (sz0.L 0), ∑ b' : Zd 3 (sz0.L 0),
          if zdistInf 3 (sz0.L 0) (a' - a) ≤ 1 ∧ zdistInf 3 (sz0.L 0) (b' - b) ≤ 1 then
            ‖loopPM 3 (sz0.L 0) (sz0.W 0) E u (sz0.seqHflow 0 u ω) b' a'‖ else 0) +
        if zdistInf 3 (sz0.L 0) (a - b) ≤ 1 then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0 :=
  ⟨gexRHS_nonneg _ _ _ _ _, maxLoopPM_nonneg _ _ _, gexRHS_swap_eq _ _ _ _ _⟩

/-- **`offSq_le_gexRHS_swap_W1`, instantiated** at `d = 3`, `L = 3`, `W = 1`, `M = 0` and the
distinct points `p = 0`, `q = e₀`. -/
theorem inst_offSq_W1 :
    offSq 3 3 1 (1 / 2) 0 (0 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) (0 : Idx 3 3 1) (Pi.single 0 1) ≤
      gexRHS 3 3 1 (1 / 2) 0 (0 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ)
        (split 3 3 1 (Pi.single 0 1)).1 (split 3 3 1 (0 : Idx 3 3 1)).1 :=
  offSq_le_gexRHS_swap_W1 _ Matrix.isHermitian_zero _ _

/-- **`perTimeDomAt_of_nonpos`, instantiated** on the model measure of `sz0`: `-1 ≺ 1` per time over
the blocks. -/
theorem inst_perTimeDomAt_of_nonpos :
    PerTimeDomAt sz0.seqP sz0.size (U := fun n => Zd 3 (sz0.L n))
      (fun _ _ _ => (-1 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  perTimeDomAt_of_nonpos _ _ _ _ (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num)

/-- **The bridges with no stochastic premise**, at `t ≡ 0` (`G_0 = m I`, so the premises are
proved by `conclusions_time_zero`, `asGMcSeq_time_zero`): `stGijGEX_of_gijOmegaSeq`,
`stGiiGEX_of_omegaSeq`, `giiOmegaSeq_of_stGiiGEX`, `asGMcSeq_iff_prec`, `gavLDetSeq_iff_prec` on
the section-3 sequence `sz0` (`N_n = (W_n L_n)^3 → ∞`, non-constant energy `lemE z_n`). -/
theorem inst_bridges_time_zero {c : ℝ} (hc : 0 < c) (Ψ : ℕ → ℝ) :
    STGijGEX sz0 (STflowE z0) (fun _ => 0) c ∧ STGiiGEX sz0 (STflowE z0) (fun _ => 0) c ∧
      GiiOmegaSeq sz0 (STflowE z0) (fun _ => 0) c ∧
      sz0.Prec (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n p ω => ‖STGM sz0 n (STflowE z0 n) ((fun _ => (0 : ℝ)) n) ω p.1 p.2‖)
        (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-c)) ∧
      sz0.Prec (U := fun n => Zd 3 (sz0.L n))
        (fun n a ω => ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (0 : ℝ)) n) (fun _ : Fin 1 => true)
          (fun _ => a) ω - mE (STflowE z0 n)‖)
        (fun n _ _ => Ψ n ^ 2) := by
  have hE : ∀ n, |STflowE z0 n| ≤ 2 := fun n => (abs_lemE_lt_two (z0_im_pos n)).le
  have h0 := conclusions_time_zero sz0 hE c Ψ
  have hGii : STGiiGEX sz0 (STflowE z0) (fun _ => 0) c :=
    stGiiGEX_of_omegaSeq sz0 sz0_admissible hE hc h0.2.1 h0.1
  exact ⟨stGijGEX_of_gijOmegaSeq sz0 h0.1, hGii, giiOmegaSeq_of_stGiiGEX sz0 hGii,
    (asGMcSeq_iff_prec sz0 (STflowE z0) (fun _ => 0) c).1 (asGMcSeq_time_zero sz0 hE c),
    (gavLDetSeq_iff_prec sz0 (STflowE z0) (fun _ => 0) Ψ).1 h0.2.2.2.2.1⟩

/-- **`asGMcPT_iff_forall_prec`, instantiated** at `s ≡ 0`, `t ≡ 1/16`, `c = 1/20`. -/
theorem inst_asGMcPT_iff :
    AsGMcPT sz0 (STflowE z0) sInst tInst (1 / 20) ↔
      ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (sInst n) (tInst n)) →
        sz0.Prec (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
          (fun n p ω => ‖STGM sz0 n (STflowE z0 n) (u n) ω p.1 p.2‖)
          (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ))) :=
  asGMcPT_iff_forall_prec sz0 (fun n => by simp only [sInst, tInst]; norm_num) (1 / 20)

/-- **`prec_maxLoop2_of_loopDetSeq`, instantiated** at `Ψ_n = W_n^{-1}`; `LoopDetSeq` is the
hypothesis. -/
theorem inst_prec_maxLoop2
    (h : LoopDetSeq sz0 (STflowE z0) tInst (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)))) :
    sz0.Prec (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2 sz0 n (STflowE z0 n) (tInst n) ω)
      (fun n _ _ => (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2) :=
  prec_maxLoop2_of_loopDetSeq sz0 h

end Instance

end RBM.Green
