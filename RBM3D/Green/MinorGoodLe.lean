/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.FlucIterGain
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Topology.Instances.Matrix

/-!
# The higher-order minor expansion and the level-budgeted minor good event, `d ≥ 3` (S1-22)

ST-1 ticket T2105.  Port of RBM2D `Green/FlucIterHigh.lean` (970 lines) and
`Green/MinorGoodLe.lean` (474 lines) at commit `c9a24cf` to the fine lattice `Z_{WL}^d`, with the
renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md` (item 2): `d : Sizes` becomes `sz : Sizes d`,
`Idx (d.L n) (d.W n)` becomes `Idx d (sz.L n) (sz.W n)`, `Coord` becomes `CoordF`, `spectralZ E t`
and `spectralM E` become `zt E t` and `mE E`.  The paper (arXiv:2507.20274) states neither
higher-order minor expansions nor minors `G^{(S)}`: `paper/tex/3_5_Loop_Hierarchy.tex:37` defers
the estimates of `lem_GbEXP` (among them `(GavLGEX)`, `3_5:33`) to Lemma 4.1 of `[YY_25]`, whose
proof is dimension-independent; the event `Ω(t, ε₀) := {‖G_t - M‖_max ≤ W^{-ε₀}}` is
`def_asGMc` (`3_5:16`), here `GoodEvent (G_t) m Ψ` (`Green/EntryCore.lean`, threshold `Ψ`).
The equation numbers (4.1)-(4.3) and (4.9) quoted below are those of `[YY_25]` (the numbering used
by RBM2D `Green/Minor.lean` and `Green/MinorGoodLe.lean`), not equations of arXiv:2507.20274:
(4.1) is `GoodEvent`, (4.2)-(4.3) the off-diagonal and diagonal estimates, (4.9) the minor formula.

## Part 1: the minor expansion (RBM2D `Green/FlucIterHigh.lean`)

`Green/FlucIterGain.lean` (T2096) reduces the moment bound for `flucAvg` to the gain interface
`FlucGainUpTo'`: `q ≤ M` conditional fluctuations `Q_{κ_1} ⋯ Q_{κ_q}` (distinct rows, all
different from `k`) applied to `Z_k = (1 - E_k)(G_{kk} - m)` gain a factor `ρ^q`, for at most `K`
slots.  This part turns that hypothesis into a statement about the `q`-fold **minor difference**
alone.

* `Finset`-indexed minors: `AgreeOffRows`, `FinDepOffRows`, `offRowsCoords`,
  `finDepOffRows_of_minorSet` (anything read off the minor `H_u^{(S)}` is strictly independent of
  every row of `S`), `greenSetMat` (`G^{(S)}`, total in `ω`), `gEnt` (`G^{(S)}_{ab}` extended by
  `0`), `greenSetMat_empty_apply`, `greenSetMat_insert_apply` ((4.9) between `G^{(S)}` and
  `G^{(S ∪ {κ})}`).
* The exact identity `applyOps_eq_applyOps_minorDiff`:
  `applyOps L (Y ∅) = applyOps L (Δ_{κ_1} ⋯ Δ_{κ_m} Y)`, `κ_1, …, κ_m` the rows carrying a `Q` in
  `L` (`qList L`).  No truncation and no indicator is used.
* Crude bounds: `norm_minorDiff_le` (each difference at most doubles a uniform bound) and the
  envelope `‖Z^{(S)}_k‖ ≤ 2 (η_t⁻¹ + 1)` (`norm_flucDiagSet_le_env`).
* **Target 1**: `flucGainUpTo'_of_minorDiffGainUpTo'`: `MinorDiffGainUpTo'` at `(B, ρ, M, K)`
  gives `FlucGainUpTo'` at the same `(B, ρ, M, K)`.  `MinorDiffGainUpTo'` is a **hypothesis** of
  the endpoint: its proof (the size of the iterated minor differences) is S1-25
  (`Green/MinorDiff`, not merged), exactly as in RBM2D.

## Part 2: the minor good event (RBM2D `Green/MinorGoodLe.lean`)

`minorGoodLe_of_goodEvent` is a **pointwise implication**: at one fixed sample point `ω`, if the
full-matrix good event `GoodEvent (G_t) m Ψ` holds at `ω`, then the level-budgeted estimates
`MinorGoodLe` (`|S| ≤ M`: `det`, `diag_ne`, `inv_le`, `off_le`, `diag_sub_le`) hold at `ω` with
threshold `2Ψ`.  The recursion `Ψ_{j+1} ≤ Ψ_j + 2Ψ_j²` is closed by the invariant
`Ψ_j ≤ Ψ + 8jΨ²`, which needs `8MΨ ≤ 1`; `Ψ ≤ 1/4` gives `‖G^{(S)}_{aa}‖ ≥ 1/2`.
* **Target 2**: `minorGoodLe_of_goodEvent_flow`, the shape the flow consumes
  (`z = zt E u`, `m = mE E`).

## Dimension: nothing to replace

Neither file has an exponent or a cardinality of the index set: the dimension enters only through
the type `Idx d (sz.L n) (sz.W n)` (a `Fintype` with `DecidableEq`); the constants (`2` per `Q`,
`2` per difference, `8MΨ ≤ 1`, `Ψ ≤ 1/4`, `Ψ ↦ 2Ψ`) contain no `W`, `L`, `d`.  Neither file uses a
weight (`UniformWeight`/`BoundedWeight`), so DECISIONS §30 (D192) does not touch it: the weights
enter only through the merged `integral_norm_flucAvg_pow_le_iter_budget` (T2096), which takes a
`BoundedWeight`.  `MinorGoodLe`'s statements are pointwise in `ω` and independent of `∀ᶠ n`,
`0 ≤ s`, `ilambda` and `L^d ≤ W^K` (DECISIONS §29): the flow statement holds for every real `u`
with `(zt E u).im ≠ 0` (that is `u ≠ 1`, `|E| < 2`).

## Differences from RBM2D (residual, after the renaming)

* The private lemmas `flucIterHigh_zt_im_pos`, `flucIterHigh_norm_green_zt_le`,
  `flucIterHigh_measurable_matrix_inv_apply` restate private lemmas of `Green/LDE.lean`
  (`flucAvg_zt_im_pos`, `flucAvg_norm_green_zt_le`, `flucAvg_measurable_matrix_inv_apply`);
  `flucIterHigh_slice_apply`, `flucIterHigh_seqHflow_apply` those of `Green/RowIndep.lean`.  The
  Hermitian invertibility `isUnit_sub_smul_one_of_im_ne_zero` of RBM2D is the merged
  `RBM.isUnit_sub_smul_of_isHermitian`, the entry bound `RBM.Ind.norm_apply_le_l2_opNorm` is
  `norm_matrix_entry_le_opNorm` (`Gauss/FlowCalculus.lean`); neither of the ST-2 versions is
  imported.
* The RBM2D `Checks` sections (at `L = 3`, `W = 2`, `Z_6 × Z_6`) are replaced by the instances at
  the end of the file at `d = 3`, `L = 3`, `W = 2`, `lam = 1/2` (`N = 216`).
-/

set_option linter.style.longLine false

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

section MinorExpansion

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-! ### Private helpers -/

/-- The slice of a common sample point, evaluated at a coordinate. -/
private theorem flucIterHigh_slice_apply (ω : Sizes.SeqΩ sz) (c : CoordF d (sz.L n) (sz.W n)) :
    Sizes.slice sz n ω c = ω ⟨n, c⟩ := rfl

/-- The entries of the common-space flow. -/
private theorem flucIterHigh_seqHflow_apply (u : ℝ) (ω : Sizes.SeqΩ sz)
    (i j : Idx d (sz.L n) (sz.W n)) :
    Sizes.seqHflow sz n u ω i j
      = (Real.sqrt u : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) i j := rfl

section MatrixMeasurable

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {Θ : Type*} [MeasurableSpace Θ]

/-- Entries of `A⁻¹` are measurable in `A` (the private lemma of `FlucAvg.lean`, restated). -/
private theorem flucIterHigh_measurable_matrix_inv_apply {M : Θ → Matrix ν ν ℂ}
    (hM : Measurable M) (i j : ν) : Measurable fun ω => (M ω)⁻¹ i j := by
  have h : (fun ω => (M ω)⁻¹ i j)
      = fun ω => Ring.inverse (M ω).det * (M ω).adjugate i j := by
    funext ω; rw [Matrix.inv_def]; rfl
  rw [h]
  refine Measurable.mul ?_ ?_
  · have hinv : Measurable (Ring.inverse : ℂ → ℂ) := by
      rw [Ring.inverse_eq_inv']; exact measurable_inv
    exact hinv.comp ((continuous_id.matrix_det).measurable.comp hM)
  · exact ((continuous_id.matrix_adjugate).measurable.comp hM).eval_matrix

end MatrixMeasurable

/-! ### Sample points that agree off a `Finset` of rows -/

/-- Two sample points **agree off the rows in `S`**: every coordinate at size `n` whose index
pair avoids `S` carries the same value.  The `S = {i}` case is `RBM.Green.AgreeOffRow`. -/
def AgreeOffRows (sz : Sizes d) (n : ℕ) (S : Finset (Idx d (sz.L n) (sz.W n))) (ω ω' : Sizes.SeqΩ sz) :
    Prop :=
  ∀ (k l : Idx d (sz.L n) (sz.W n)) (b : Bool), k ∉ S → l ∉ S → ω ⟨n, k, l, b⟩ = ω' ⟨n, k, l, b⟩

/-- The entries of `X` away from the rows and columns in `S` read only coordinates that
avoid `S`. -/
theorem Xentry_congr_of_not_mem {S : Finset (Idx d (sz.L n) (sz.W n))} {ω ω' : Sizes.SeqΩ sz}
    (h : AgreeOffRows sz n S ω ω') {k l : Idx d (sz.L n) (sz.W n)} (hk : k ∉ S) (hl : l ∉ S) :
    Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω) k l
      = Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n ω') k l := by
  unfold Xentry
  simp only [flucIterHigh_slice_apply]
  split_ifs with h1 h2
  · rw [h k l true hk hl, h k l false hk hl]
  · rw [h l k true hl hk, h l k false hl hk]
  · rw [h k l true hk hl]

/-- The minor matrix of `H_u` on `{a ∉ S}` reads only coordinates that avoid `S`. -/
theorem Hflow_submatrix_set_congr (u : ℝ) {S : Finset (Idx d (sz.L n) (sz.W n))}
    {ω ω' : Sizes.SeqΩ sz} (h : AgreeOffRows sz n S ω ω') :
    (Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
      = (Sizes.seqHflow sz n u ω').submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n)) := by
  ext k l
  simp only [Matrix.submatrix_apply, flucIterHigh_seqHflow_apply]
  rw [Xentry_congr_of_not_mem h k.2 l.2]

/-! ### `FinDepOffRows`: strict independence of a whole `Finset` of rows -/

/-- **`g` is strictly independent of every row in `S`**: it reads finitely many Gaussian
coordinates, none of which is a row-`κ` coordinate for any `κ ∈ S`.  This is
`RBM.Green.FinDepOffRow` with the witness set constrained to avoid all of `S` at once. -/
def FinDepOffRows (sz : Sizes d) (n : ℕ) (S : Finset (Idx d (sz.L n) (sz.W n))) {V : Type*}
    (g : Sizes.SeqΩ sz → V) : Prop :=
  ∃ I : Finset (Sizes.SeqCoord sz), (∀ c ∈ I, ∀ κ ∈ S, ¬ IsRowCoord sz n κ c) ∧
    ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ I, ω c = ω' c) → g ω = g ω'

/-- **The annihilation half, in one line**: `FinDepOffRows S` gives `FinDepOffRow κ` for every
`κ ∈ S`, hence `E_κ` fixes `g` and `Q_κ g = 0`. -/
theorem FinDepOffRows.finDepOffRow {S : Finset (Idx d (sz.L n) (sz.W n))} {V : Type*}
    {g : Sizes.SeqΩ sz → V} (h : FinDepOffRows sz n S g) {κ : Idx d (sz.L n) (sz.W n)} (hκ : κ ∈ S) :
    FinDepOffRow sz n κ g :=
  let ⟨I, hI, hg⟩ := h; ⟨I, fun c hc => hI c hc κ hκ, hg⟩

theorem FinDepOffRows.comp {S : Finset (Idx d (sz.L n) (sz.W n))} {V W : Type*}
    {g : Sizes.SeqΩ sz → V} (h : FinDepOffRows sz n S g) (F : V → W) :
    FinDepOffRows sz n S fun ω => F (g ω) :=
  let ⟨I, hI, hg⟩ := h
  ⟨I, hI, fun ω ω' hω => show F (g ω) = F (g ω') by rw [hg ω ω' hω]⟩

theorem FinDepOffRows.sub {S : Finset (Idx d (sz.L n) (sz.W n))} {X Y : Sizes.SeqΩ sz → ℂ}
    (hX : FinDepOffRows sz n S X) (hY : FinDepOffRows sz n S Y) :
    FinDepOffRows sz n S fun ω => X ω - Y ω := by
  classical
  obtain ⟨I, hI, hX'⟩ := hX
  obtain ⟨J, hJ, hY'⟩ := hY
  refine ⟨I ∪ J, ?_, fun ω ω' hω => ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · exact hI c h
    · exact hJ c h
  · change X ω - Y ω = X ω' - Y ω'
    rw [hX' ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
      hY' ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

/-- **`E_{k}` preserves independence of every row in `S`** — the `Finset` version of
`RBM.Green.finDepOffRow_condRow`.  It is what keeps the `(1 - E_k)` in `Z^{(S)}_k` harmless. -/
theorem finDepOffRows_condRow {S : Finset (Idx d (sz.L n) (sz.W n))} {k : Idx d (sz.L n) (sz.W n)}
    {X : Sizes.SeqΩ sz → ℂ} (h : FinDepOffRows sz n S X) :
    FinDepOffRows sz n S (condRow sz n k X) := by
  classical
  obtain ⟨I, hI, hX⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord sz n k c, fun c hc => hI c (Finset.mem_filter.1 hc).1,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hX _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord sz n k c
  · rw [rowSplit_apply_of_isRowCoord k ω ω'' hcr, rowSplit_apply_of_isRowCoord k ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

theorem finDepOffRows_qRow {S : Finset (Idx d (sz.L n) (sz.W n))} {k : Idx d (sz.L n) (sz.W n)}
    {X : Sizes.SeqΩ sz → ℂ} (h : FinDepOffRows sz n S X) :
    FinDepOffRows sz n S (qRow sz n k X) :=
  h.sub (finDepOffRows_condRow h)

/-- The witness set: every coordinate at size `n` whose index pair avoids `S`. -/
def offRowsCoords (sz : Sizes d) (n : ℕ) (S : Finset (Idx d (sz.L n) (sz.W n))) :
    Finset (Sizes.SeqCoord sz) :=
  (Finset.univ.image fun p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool =>
      (⟨n, p⟩ : Sizes.SeqCoord sz)).filter
    fun c => ∀ κ ∈ S, ¬ IsRowCoord sz n κ c

theorem forall_not_isRowCoord_of_mem_offRowsCoords {S : Finset (Idx d (sz.L n) (sz.W n))}
    {c : Sizes.SeqCoord sz} (hc : c ∈ offRowsCoords sz n S) : ∀ κ ∈ S, ¬ IsRowCoord sz n κ c :=
  (Finset.mem_filter.1 hc).2

theorem mem_offRowsCoords {S : Finset (Idx d (sz.L n) (sz.W n))} {i j : Idx d (sz.L n) (sz.W n)}
    {b : Bool} (hi : i ∉ S) (hj : j ∉ S) :
    (⟨n, i, j, b⟩ : Sizes.SeqCoord sz) ∈ offRowsCoords sz n S := by
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(i, j, b), Finset.mem_univ _, rfl⟩, ?_⟩
  intro κ hκ
  simp only [isRowCoord_mk]
  rintro (h | h)
  · exact hi (h ▸ hκ)
  · exact hj (h ▸ hκ)

/-- **The master row-independence lemma for a `Finset` of rows.**  Anything read off the minor
matrix `H_u^{(S)}` is strictly independent of every row in `S`. -/
theorem finDepOffRows_of_minorSet (sz : Sizes d) (n : ℕ) (u : ℝ) (S : Finset (Idx d (sz.L n) (sz.W n)))
    {V : Type*}
    (F : Matrix {a : Idx d (sz.L n) (sz.W n) // a ∉ S} {a : Idx d (sz.L n) (sz.W n) // a ∉ S} ℂ → V) :
    FinDepOffRows sz n S fun ω =>
      F ((Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))) := by
  refine ⟨offRowsCoords sz n S, fun c hc => forall_not_isRowCoord_of_mem_offRowsCoords hc,
    fun ω ω' hω => ?_⟩
  have hagree : AgreeOffRows sz n S ω ω' := fun i j b hi hj => hω _ (mem_offRowsCoords hi hj)
  change F _ = F _
  rw [Hflow_submatrix_set_congr u hagree]

/-! ### The iterated minor resolvent `G^{(S)}` -/

/-- **`G^{(S)} = (H_u^{(S)} - z)⁻¹`**, the resolvent on `{a ∉ S}`, as a *total* function of `ω`
(`Matrix.inv` is total, so no invertibility hypothesis is carried).  For `S = ∅` it is the full
resolvent (`greenSetMat_empty_apply`); for `S = {κ}` it is `RBM.Green.greenMinorMat` on the
index set `{a // a ∉ {κ}}` in place of `{a // a ≠ κ}` (this identification is not proved here). -/
noncomputable def greenSetMat (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz) :
    Matrix {a : Idx d (sz.L n) (sz.W n) // a ∉ S} {a : Idx d (sz.L n) (sz.W n) // a ∉ S} ℂ :=
  ((Sizes.seqHflow sz n u ω).submatrix
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ∉ S} {a : Idx d (sz.L n) (sz.W n) // a ∉ S}
        ℂ))⁻¹

theorem greenSetMat_eq_green_submatrix (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz) :
    greenSetMat sz n u z S ω
      = green ((Sizes.seqHflow sz n u ω).submatrix
          (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
          (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))) z := rfl

theorem finDepOffRows_greenSetMat (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx d (sz.L n) (sz.W n))) :
    FinDepOffRows sz n S (greenSetMat sz n u z S) :=
  finDepOffRows_of_minorSet sz n u S fun M => (M - z • 1)⁻¹

theorem finDepOffRows_greenSetMat_apply (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx d (sz.L n) (sz.W n))) (a b : {a : Idx d (sz.L n) (sz.W n) // a ∉ S}) :
    FinDepOffRows sz n S fun ω => greenSetMat sz n u z S ω a b :=
  (finDepOffRows_greenSetMat sz n u z S).comp fun M => M a b

theorem measurable_greenSetMat_apply (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx d (sz.L n) (sz.W n))) (a b : {a : Idx d (sz.L n) (sz.W n) // a ∉ S}) :
    Measurable fun ω => greenSetMat sz n u z S ω a b := by
  refine flucIterHigh_measurable_matrix_inv_apply (M := fun ω : Sizes.SeqΩ sz =>
    (Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
      (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ∉ S}
        {a : Idx d (sz.L n) (sz.W n) // a ∉ S} ℂ)) ?_ a b
  refine Matrix.measurable_iff.2 fun p q => ?_
  have h : (fun ω : Sizes.SeqΩ sz =>
      ((Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ∉ S} → Idx d (sz.L n) (sz.W n))
        - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ∉ S}
          {a : Idx d (sz.L n) (sz.W n) // a ∉ S} ℂ)) p q)
      = fun ω => Sizes.seqHflow sz n u ω p.1 q.1
          - z * (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ∉ S}
            {a : Idx d (sz.L n) (sz.W n) // a ∉ S} ℂ) p q := by
    funext ω; simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  exact (Sizes.measurable_seqHflow_entry sz n u p.1 q.1).sub measurable_const

/-! ### The entries of the iterated minor, extended by `0`

`greenSetMat` lives on the subtype `{a // a ∉ S}`, so its entries carry a proof that the index
has not been removed.  `gEnt` erases that proof by extending the entry by `0` to the levels that
*have* removed `a` or `b`.  This is what makes the difference calculus total: no side condition
travels with the recursion.  It is stated here so that `RBM2D/Green/MinorGoodLe.lean`, which needs
`gEnt` to phrase the level-budgeted good event, does not have to import the minor-difference
calculus of G4.6, which consumes that event. -/

section GEnt

variable {u : ℝ} {z : ℂ} {ω : Sizes.SeqΩ sz} {a b : Idx d (sz.L n) (sz.W n)}
  {S : Finset (Idx d (sz.L n) (sz.W n))}

/-- `G^{(S)}_{ab}`, extended by `0` to the levels that have removed `a` or `b`.  The extension is
what makes the difference calculus total: no side condition is carried along the recursion. -/
noncomputable def gEnt (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
    (a b : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) : ℂ :=
  if ha : a ∉ S then (if hb : b ∉ S then greenSetMat sz n u z S ω ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0

theorem gEnt_apply (ha : a ∉ S) (hb : b ∉ S) :
    gEnt sz n u z ω a b S = greenSetMat sz n u z S ω ⟨a, ha⟩ ⟨b, hb⟩ := by
  rw [gEnt, dite_eq_left ha, dite_eq_left hb]

theorem gEnt_eq_zero_left (h : a ∈ S) : gEnt sz n u z ω a b S = 0 := by
  rw [gEnt, dite_eq_right (not_not_intro h)]

theorem gEnt_eq_zero_right (h : b ∈ S) : gEnt sz n u z ω a b S = 0 := by
  rw [gEnt]
  by_cases ha : a ∉ S
  · rw [dite_eq_left ha, dite_eq_right (not_not_intro h)]
  · rw [dite_eq_right ha]

end GEnt

/-! ### The `m`-fold minor difference

The gain comes from the *iterated* difference operator `Δ_{κ_1} ⋯ Δ_{κ_m}`, where
`Δ_κ X^{(S)} := X^{(S)} - X^{(S ∪ {κ})}`.  It is presented as a recursion on the list of rows,
acting on a whole *family* `Y : Finset (Idx) → Ω → ℂ` of minor versions; unfolded, it is the
inclusion–exclusion sum `∑_{T ⊆ {κ_1,…,κ_m}} (-1)^{#T} Y T`. -/

/-- `minorDiff sz n [κ_1, …, κ_m] Y = Δ_{κ_1} ⋯ Δ_{κ_m} Y`, the `m`-fold minor difference of
the family `Y`. -/
noncomputable def minorDiff (sz : Sizes d) (n : ℕ) :
    List (Idx d (sz.L n) (sz.W n)) → (Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) →
      (Sizes.SeqΩ sz → ℂ)
  | [], Y => Y ∅
  | κ :: l, Y => minorDiff sz n l fun S ω => Y S ω - Y (insert κ S) ω

@[simp] theorem minorDiff_nil (sz : Sizes d) (n : ℕ)
    (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) :
    minorDiff sz n [] Y = Y ∅ := rfl

@[simp] theorem minorDiff_cons (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n))
    (l : List (Idx d (sz.L n) (sz.W n)))
    (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) :
    minorDiff sz n (κ :: l) Y = minorDiff sz n l fun S ω => Y S ω - Y (insert κ S) ω := rfl

/-- The rows carrying a `Q` in a word, in order.  These are exactly the rows along which the
minor difference is taken. -/
def qList (L : List (Bool × Idx d (sz.L n) (sz.W n))) : List (Idx d (sz.L n) (sz.W n)) :=
  (L.filter (·.1)).map Prod.snd

@[simp] theorem qList_cons_true (κ : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) :
    qList ((true, κ) :: l) = κ :: qList l := rfl

@[simp] theorem qList_cons_false (κ : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) :
    qList ((false, κ) :: l) = qList l := rfl

theorem length_qList (L : List (Bool × Idx d (sz.L n) (sz.W n))) : (qList L).length = numQ L := by
  simp [qList, numQ, List.countP_eq_length_filter]

/-! ### Linearity of the words, and their independence -/

theorem qRow_sub (k : Idx d (sz.L n) (sz.W n)) {X Y : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X)
    (hY : BddMeas sz Y) :
    qRow sz n k (fun ω => X ω - Y ω) = fun ω => qRow sz n k X ω - qRow sz n k Y ω := by
  funext ω
  change X ω - Y ω - condRow sz n k (fun ω' => X ω' - Y ω') ω
    = (X ω - condRow sz n k X ω) - (Y ω - condRow sz n k Y ω)
  rw [condRow_sub k (hX.rowIntegrable k) (hY.rowIntegrable k)]
  ring

/-- **The words are linear.** -/
theorem applyOps_sub (l : List (Bool × Idx d (sz.L n) (sz.W n))) {X Y : Sizes.SeqΩ sz → ℂ}
    (hX : BddMeas sz X) (hY : BddMeas sz Y) :
    applyOps sz n l (fun ω => X ω - Y ω)
      = fun ω => applyOps sz n l X ω - applyOps sz n l Y ω := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [applyOps_cons_false, ih]
        exact condRow_sub κ ((hX.applyOps l).rowIntegrable κ)
          ((hY.applyOps l).rowIntegrable κ)
      · rw [applyOps_cons_true, ih]
        exact qRow_sub κ (hX.applyOps l) (hY.applyOps l)

/-- **A word preserves strict independence of row `κ`.** -/
theorem finDepOffRow_applyOps {κ : Idx d (sz.L n) (sz.W n)}
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) {X : Sizes.SeqΩ sz → ℂ}
    (h : FinDepOffRow sz n κ X) : FinDepOffRow sz n κ (applyOps sz n l X) := by
  induction l with
  | nil => simpa using h
  | cons x l ih =>
      obtain ⟨b, ν⟩ := x
      cases b
      · simpa only [applyOps_cons_false] using finDepOffRow_condRow (k' := ν) ih
      · rw [applyOps_cons_true]
        exact ih.sub (finDepOffRow_condRow (k' := ν) ih)

/-! ### The annihilation identity

This is the whole content of the higher-order expansion on the probabilistic side, and it is an
**exact identity**, not an estimate: a word may be applied to the `m`-fold minor difference
instead of to the function itself, where `m` is the number of `Q`'s in the word. -/

/-- **`applyOps L (Y ∅) = applyOps L (Δ_{κ_1} ⋯ Δ_{κ_m} Y)`**, where `κ_1, …, κ_m` are the rows
carrying a `Q` in `L`.

The proof peels the outermost letter.  A `P` letter passes through by the inductive hypothesis.
For a `Q_κ` letter, replace the family `Y` by `Z S := Y S - Y (S ∪ {κ})`: by linearity of the
word, `applyOps l (Z ∅) = applyOps l (Y ∅) - applyOps l (Y {κ})`, and the subtracted term is
killed outright by `Q_κ`, because `Y {κ}` is strictly independent of row `κ` and a word
preserves that.  No estimate, no truncation, no indicator. -/
theorem applyOps_eq_applyOps_minorDiff (L : List (Bool × Idx d (sz.L n) (sz.W n)))
    (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) (hbdd : ∀ S, BddMeas sz (Y S))
    (hind : ∀ (S : Finset (Idx d (sz.L n) (sz.W n))), ∀ κ ∈ S, FinDepOffRow sz n κ (Y S)) :
    applyOps sz n L (Y ∅) = applyOps sz n L (minorDiff sz n (qList L) Y) := by
  induction L generalizing Y with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [qList_cons_false, applyOps_cons_false, applyOps_cons_false, ih Y hbdd hind]
      · set Z : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ :=
          fun S ω => Y S ω - Y (insert κ S) ω with hZ
        have hbddZ : ∀ S, BddMeas sz (Z S) := fun S => (hbdd S).sub (hbdd _)
        have hindZ : ∀ (S : Finset (Idx d (sz.L n) (sz.W n))), ∀ ν ∈ S, FinDepOffRow sz n ν (Z S) :=
          fun S ν hν => (hind S ν hν).sub (hind _ ν (Finset.mem_insert_of_mem hν))
        have hkey : applyOps sz n l (Z ∅)
            = fun ω => applyOps sz n l (Y ∅) ω - applyOps sz n l (Y {κ}) ω := by
          have hins : insert κ (∅ : Finset (Idx d (sz.L n) (sz.W n))) = {κ} := rfl
          rw [hZ]
          simpa only [hins] using applyOps_sub l (hbdd ∅) (hbdd {κ})
        have hann : qRow sz n κ (applyOps sz n l (Y {κ})) = 0 := by
          funext ω
          have hf : FinDepOffRow sz n κ (applyOps sz n l (Y {κ})) :=
            finDepOffRow_applyOps l (hind {κ} κ (Finset.mem_singleton_self κ))
          change applyOps sz n l (Y {κ}) ω - condRow sz n κ (applyOps sz n l (Y {κ})) ω = 0
          rw [congrFun (condRow_of_finDepOffRow hf) ω, sub_self]
        rw [qList_cons_true, minorDiff_cons, applyOps_cons_true, applyOps_cons_true,
          ← hZ, ← ih Z hbddZ hindZ, hkey,
          qRow_sub κ ((hbdd ∅).applyOps l) ((hbdd {κ}).applyOps l), hann]
        funext ω
        simp

/-! ### The concrete family of iterated minors of `Z_k` -/

/-- `G^{(S)}_{kk} - m`, extended by `0` to the (never used) subsets containing `k`. -/
noncomputable def greenSetDiagCentered (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) : Sizes.SeqΩ sz → ℂ :=
  fun ω => if h : k ∉ S then greenSetMat sz n u z S ω ⟨k, h⟩ ⟨k, h⟩ - m else 0

/-- **`Z^{(S)}_k := (1 - E_k)(G^{(S)}_{kk} - m)`**, the `S`-minor version of the fluctuation.
`S = ∅` is `RBM.Green.flucDiag` (`flucDiagSet_empty`). -/
noncomputable def flucDiagSet (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (k : Idx d (sz.L n) (sz.W n))
    (S : Finset (Idx d (sz.L n) (sz.W n))) : Sizes.SeqΩ sz → ℂ :=
  qRow sz n k (greenSetDiagCentered sz n u z m k S)

theorem finDepOffRows_greenSetDiagCentered (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) :
    FinDepOffRows sz n S (greenSetDiagCentered sz n u z m k S) := by
  unfold greenSetDiagCentered
  by_cases h : k ∉ S
  · simp only [dite_eq_left h]
    exact (finDepOffRows_greenSetMat_apply sz n u z S ⟨k, h⟩ ⟨k, h⟩).comp fun c => c - m
  · simp only [dite_eq_right h]
    exact ⟨∅, by simp, fun _ _ _ => rfl⟩

theorem finDepOffRows_flucDiagSet (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) :
    FinDepOffRows sz n S (flucDiagSet sz n u z m k S) :=
  finDepOffRows_qRow (finDepOffRows_greenSetDiagCentered sz n u z m k S)

/-- The hypothesis `hind` of `applyOps_eq_applyOps_minorDiff`, for the concrete family. -/
theorem finDepOffRow_flucDiagSet (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) {κ : Idx d (sz.L n) (sz.W n)}
    (hκ : κ ∈ S) : FinDepOffRow sz n κ (flucDiagSet sz n u z m k S) :=
  (finDepOffRows_flucDiagSet sz n u z m k S).finDepOffRow hκ

/-! #### `S = ∅` is the full resolvent -/

theorem greenSetMat_empty_apply (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
    (a b : {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))}) :
    greenSetMat sz n u z ∅ ω a b = green (Sizes.seqHflow sz n u ω) z a.1 b.1 := by
  classical
  set e : {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))}
      ≃ Idx d (sz.L n) (sz.W n) :=
    Equiv.subtypeUnivEquiv fun x => Finset.notMem_empty x with he
  have hone : ∀ i j : {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))},
      (1 : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))}
        {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))} ℂ) i j
        = (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) i.1 j.1 := by
    intro i j
    by_cases h : i = j
    · subst h; simp
    · have h' : i.1 ≠ j.1 := fun hh => h (Subtype.ext hh)
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h']
  have hsub : (Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))} →
          Idx d (sz.L n) (sz.W n)) Subtype.val
        - z • (1 : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))}
          {x : Idx d (sz.L n) (sz.W n) // x ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n)))} ℂ)
      = (Sizes.seqHflow sz n u ω
          - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)).submatrix ⇑e ⇑e := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.submatrix_apply, smul_eq_mul, he,
      Equiv.subtypeUnivEquiv_apply]
    rw [hone i j]
  change (_ : Matrix _ _ ℂ)⁻¹ a b = _
  rw [hsub, Matrix.inv_submatrix_equiv]
  simp [green, he]

theorem flucDiagSet_empty (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (k : Idx d (sz.L n) (sz.W n)) :
    flucDiagSet sz n u z m k ∅ = flucDiag sz n u z m k := by
  have hg : greenSetDiagCentered sz n u z m k ∅ = greenDiagCentered sz n u z m k := by
    funext ω
    have hk : k ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n))) := Finset.notMem_empty k
    change (if h : k ∉ (∅ : Finset (Idx d (sz.L n) (sz.W n))) then
        greenSetMat sz n u z ∅ ω ⟨k, h⟩ ⟨k, h⟩ - m else 0) = _
    rw [dite_eq_left hk, greenSetMat_empty_apply]
    rfl
  rw [flucDiagSet, hg, flucDiag_eq_qRow]

/-! ### One step of (4.9) between consecutive iterated minors

`RBM2D/Green/Minor.lean` proves (4.9) for an arbitrary `Fintype` index, so it iterates:
removing one more row `κ` from `G^{(S)}` gives `G^{(S ∪ {κ})}`, and the two differ by the rank-one
term `G^{(S)}_{aκ} G^{(S)}_{κb} / G^{(S)}_{κκ}`.  The only work is the index bookkeeping. -/

/-- Removing `κ` from `{a ∉ S}` is passing to `{a ∉ insert κ S}`. -/
def insertRowEquiv (sz : Sizes d) (n : ℕ) {S : Finset (Idx d (sz.L n) (sz.W n))}
    {κ : Idx d (sz.L n) (sz.W n)} (hκ : κ ∉ S) :
    {y : {x : Idx d (sz.L n) (sz.W n) // x ∉ S} // y ≠ ⟨κ, hκ⟩}
      ≃ {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S} where
  toFun y := ⟨y.1.1, by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => y.2 (Subtype.ext h), y.1.2⟩⟩
  invFun x := ⟨⟨x.1, fun h => x.2 (Finset.mem_insert_of_mem h)⟩, by
    intro h
    exact x.2 (by rw [show x.1 = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl

/-- **(4.9) between `G^{(S)}` and `G^{(S ∪ {κ})}`.**  The hypotheses are the ones (4.9) itself
needs: the `S`-minor is invertible and its `κκ` entry does not vanish — on the event (4.1) the
latter is `≥ 1/2` (`RBM.Green.GoodEvent.half_le_norm_diag`). -/
theorem greenSetMat_insert_apply (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz) {κ : Idx d (sz.L n) (sz.W n)}
    (hκ : κ ∉ S)
    (hdet : IsUnit ((Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {x : Idx d (sz.L n) (sz.W n) // x ∉ S} → Idx d (sz.L n) (sz.W n)) Subtype.val
        - z • (1 : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ S}
          {x : Idx d (sz.L n) (sz.W n) // x ∉ S} ℂ)).det)
    (hGκκ : greenSetMat sz n u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0)
    {a b : Idx d (sz.L n) (sz.W n)} (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    greenSetMat sz n u z (insert κ S) ω ⟨a, ha⟩ ⟨b, hb⟩
      = greenSetMat sz n u z S ω ⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩
            ⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩
        - greenSetMat sz n u z S ω ⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩ ⟨κ, hκ⟩
            * greenSetMat sz n u z S ω ⟨κ, hκ⟩
              ⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩
            / greenSetMat sz n u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ := by
  classical
  set ν := {x : Idx d (sz.L n) (sz.W n) // x ∉ S}
  set M : Matrix ν ν ℂ := (Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : ν → Idx d (sz.L n) (sz.W n)) Subtype.val - z • (1 : Matrix ν ν ℂ) with hM
  set G : Matrix ν ν ℂ := greenSetMat sz n u z S ω with hG
  have hGM : G * M = 1 := Matrix.nonsing_inv_mul M hdet
  set i : ν := ⟨κ, hκ⟩ with hi
  set e := insertRowEquiv sz n hκ with he
  set A : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S}
      {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S} ℂ :=
    (Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S} → Idx d (sz.L n) (sz.W n))
      Subtype.val - z • 1 with hA
  have hminor : minorMat M i = A.submatrix ⇑e ⇑e := by
    ext y w
    have hone : (1 : Matrix ν ν ℂ) y.1 w.1
        = (1 : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S}
            {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S} ℂ)
            (e y) (e w) := by
      by_cases h : y.1.1 = w.1.1
      · have h1 : y.1 = w.1 := Subtype.ext h
        have h2 : e y = e w := Subtype.ext h
        rw [h1, h2, Matrix.one_apply_eq, Matrix.one_apply_eq]
      · have h1 : y.1 ≠ w.1 := fun hh => h (congrArg Subtype.val hh)
        have h2 : e y ≠ e w := fun hh =>
          h (congrArg (fun x : {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S} => x.1) hh)
        rw [Matrix.one_apply_ne h1, Matrix.one_apply_ne h2]
    simp only [minorMat_apply, hM, hA, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.submatrix_apply, smul_eq_mul]
    rw [hone]
    rfl
  have hinv : minorGreen G i = (greenSetMat sz n u z (insert κ S) ω).submatrix ⇑e ⇑e := by
    rw [← inv_minorMat hGM i hGκκ, hminor, Matrix.inv_submatrix_equiv]
    rfl
  have hane : (⟨a, fun h => ha (Finset.mem_insert_of_mem h)⟩ : ν) ≠ i := by
    intro h
    exact ha (by rw [show a = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have hbne : (⟨b, fun h => hb (Finset.mem_insert_of_mem h)⟩ : ν) ≠ i := by
    intro h
    exact hb (by rw [show b = κ from congrArg Subtype.val h]; exact Finset.mem_insert_self κ S)
  have := congrFun (congrFun hinv ⟨_, hane⟩) ⟨_, hbne⟩
  simp only [minorGreen_apply, Matrix.submatrix_apply] at this
  rw [show (e ⟨_, hane⟩ : {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S}) = ⟨a, ha⟩
      from Subtype.ext rfl,
    show (e ⟨_, hbne⟩ : {x : Idx d (sz.L n) (sz.W n) // x ∉ insert κ S}) = ⟨b, hb⟩
      from Subtype.ext rfl] at this
  exact this.symm

/-! ### Crude bounds on the difference, and the deterministic envelope -/

/-- Each difference at most doubles a uniform bound. -/
theorem norm_minorDiff_le (l : List (Idx d (sz.L n) (sz.W n)))
    (Y : Finset (Idx d (sz.L n) (sz.W n)) → Sizes.SeqΩ sz → ℂ) {b : ℝ}
    (hb : ∀ S ω, ‖Y S ω‖ ≤ b) (ω : Sizes.SeqΩ sz) :
    ‖minorDiff sz n l Y ω‖ ≤ 2 ^ l.length * b := by
  induction l generalizing Y b with
  | nil => simpa using hb ∅ ω
  | cons κ l ih =>
      have hb' : ∀ (S : Finset (Idx d (sz.L n) (sz.W n))) (ω' : Sizes.SeqΩ sz),
          ‖(fun S ω => Y S ω - Y (insert κ S) ω) S ω'‖ ≤ 2 * b := fun S ω' =>
        le_trans (norm_sub_le _ _) (by linarith [hb S ω', hb (insert κ S) ω'])
      have := ih (fun S ω => Y S ω - Y (insert κ S) ω) hb'
      rw [minorDiff_cons]
      calc ‖minorDiff sz n l (fun S ω => Y S ω - Y (insert κ S) ω) ω‖
          ≤ 2 ^ l.length * (2 * b) := this
        _ = 2 ^ (κ :: l).length * b := by rw [List.length_cons, pow_succ]; ring

section Env

open scoped Matrix.Norms.L2Operator

variable {E t : ℝ}

/-- For `|E| < 2` and `t < 1`, `η_t = Im z_t > 0` (the private lemma of `FlucAvg.lean`,
restated). -/
private theorem flucIterHigh_zt_im_pos (hE : |E| < 2) (ht : t < 1) :
    0 < (zt E t).im := by
  rw [zt_im]
  exact mul_pos (by linarith) (mE_im_pos hE)

/-- The merged `Gres H z +` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹` (the private lemma
`flucAvg_Gres_true_eq_green` of `Green/LDE.lean`, restated). -/
private theorem flucIterHigh_Gres_true_eq_green {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (z : ℂ) : Gres H z true = green H z := by
  simp only [green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- The Green function of a Hermitian matrix at `z_t` has operator norm at most `η_t⁻¹` (the
private lemma `flucAvg_norm_green_zt_le` of `Green/LDE.lean`, restated; RBM2D `norm_green_le`,
`Gauss/Envelope.lean:116`, read through `norm_Gsig_le_inv_eta`). -/
private theorem flucIterHigh_norm_green_zt_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (hE : |E| < 2) (ht : t < 1) :
    ‖green H (zt E t)‖ ≤ ((zt E t).im)⁻¹ := by
  have hη := flucIterHigh_zt_im_pos hE ht
  have h := norm_Gsig_le_inv_eta hH hη (le_of_eq (abs_of_pos hη).symm) true
  rwa [flucIterHigh_Gres_true_eq_green] at h

/-- `|G^{(S)}_{ab}| ≤ η_t⁻¹` for every `ω`: `H^{(S)}` is a minor of a Hermitian matrix. -/
theorem norm_greenSetMat_apply_le_etaT (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {S : Finset (Idx d (sz.L n) (sz.W n))} (a b : {x : Idx d (sz.L n) (sz.W n) // x ∉ S})
    (ω : Sizes.SeqΩ sz) :
    ‖greenSetMat sz n u (zt E t) S ω a b‖ ≤ ((zt E t).im)⁻¹ := by
  rw [greenSetMat_eq_green_submatrix]
  exact le_trans (norm_matrix_entry_le_opNorm _ a b)
    (flucIterHigh_norm_green_zt_le
      ((Sizes.seqHflow_isHermitian sz n u ω).submatrix _) hE ht)

theorem measurable_greenSetDiagCentered (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) :
    Measurable (greenSetDiagCentered sz n u z m k S) := by
  unfold greenSetDiagCentered
  by_cases h : k ∉ S
  · simp only [dite_eq_left h]
    exact (measurable_greenSetMat_apply sz n u z S ⟨k, h⟩ ⟨k, h⟩).sub measurable_const
  · simp only [dite_eq_right h]
    exact measurable_const

theorem norm_greenSetDiagCentered_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz) :
    ‖greenSetDiagCentered sz n u (zt E t) (mE E) k S ω‖
      ≤ ((zt E t).im)⁻¹ + 1 := by
  have hη : 0 < (zt E t).im := flucIterHigh_zt_im_pos hE ht
  change ‖if h : k ∉ S then greenSetMat sz n u (zt E t) S ω ⟨k, h⟩ ⟨k, h⟩ - mE E
    else 0‖ ≤ _
  by_cases h : k ∉ S
  · rw [dite_eq_left h]
    refine le_trans (norm_sub_le _ _)
      (add_le_add (norm_greenSetMat_apply_le_etaT hE ht u ⟨k, h⟩ ⟨k, h⟩ ω) ?_)
    exact le_of_eq (norm_mE hE.le)
  · rw [dite_eq_right h, norm_zero]
    positivity

theorem bddMeas_greenSetDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) (S : Finset (Idx d (sz.L n) (sz.W n))) :
    BddMeas sz (greenSetDiagCentered sz n u (zt E t) (mE E) k S) :=
  ⟨measurable_greenSetDiagCentered sz n u (zt E t) (mE E) k S,
    ((zt E t).im)⁻¹ + 1, norm_greenSetDiagCentered_le_env hE ht u k S⟩

theorem bddMeas_flucDiagSet (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx d (sz.L n) (sz.W n))
    (S : Finset (Idx d (sz.L n) (sz.W n))) :
    BddMeas sz (flucDiagSet sz n u (zt E t) (mE E) k S) :=
  (bddMeas_greenSetDiagCentered hE ht u k S).qRow k

theorem norm_flucDiagSet_le_env (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx d (sz.L n) (sz.W n))
    (S : Finset (Idx d (sz.L n) (sz.W n))) (ω : Sizes.SeqΩ sz) :
    ‖flucDiagSet sz n u (zt E t) (mE E) k S ω‖
      ≤ 2 * (((zt E t).im)⁻¹ + 1) := by
  have h := norm_sub_condRow_le (k := k)
    (X := greenSetDiagCentered sz n u (zt E t) (mE E) k S)
    (b := ((zt E t).im)⁻¹ + 1) (norm_greenSetDiagCentered_le_env hE ht u k S) ω
  exact h

/-! ### The interface, reduced to the iterated minors

`applyOps_eq_applyOps_minorDiff` turns `FlucGainUpTo'` — a statement about the effect of `q`
conditional fluctuations — into a statement about the `q`-fold minor difference alone.  The
conditional expectations survive only as the outer word, which costs at most `2^q` and no longer
has to *produce* anything.

The budget `K` on `#ι` is that of `FlucGainUpTo'` (RBM1D: `n`): without it, `ι = Fin j` with empty
words would give `∫ ‖Z_k‖^j ≤ B^j` for every `j`, i.e. an `L^∞` bound. -/

/-- **`FlucGainUpTo'` for the reduced quantity `applyOps L (Δ_{κ_1} ⋯ Δ_{κ_q} Z^{(·)}_k)`**, with
both budgets: `M` on the word length and `K` on the number of slots `#ι`. -/
def MinorDiffGainUpTo' (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (B ρ : ℝ) (M K : ℕ) : Prop :=
  0 ≤ B ∧ 0 ≤ ρ ∧
    ∀ (ι : Type) [Fintype ι] (k : ι → Idx d (sz.L n) (sz.W n))
      (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))),
      (∀ i, ((L i).map Prod.snd).Nodup) → (∀ i, ∀ x ∈ L i, x.2 ≠ k i) →
      (∀ i, (L i).length ≤ M) → Fintype.card ι ≤ K →
      ∫ ω, ∏ i, ‖applyOps sz n (L i)
          (minorDiff sz n (qList (L i)) (flucDiagSet sz n u z m (k i))) ω‖ ∂(Sizes.seqP sz)
        ≤ B ^ Fintype.card ι * ρ ^ ∑ i, numQ (L i)

/-- **`FlucGainUpTo'` from `MinorDiffGainUpTo'`**: the rewriting step is the exact identity
`applyOps_eq_applyOps_minorDiff`, which touches neither the words nor the index type, so both
budgets and the gain `ρ^{∑ numQ}` are handed on unchanged. -/
theorem flucGainUpTo'_of_minorDiffGainUpTo' (hE : |E| < 2) (ht : t < 1) (u : ℝ) {B ρ : ℝ}
    {M K : ℕ} (h : MinorDiffGainUpTo' sz n u (zt E t) (mE E) B ρ M K) :
    FlucGainUpTo' sz n u (zt E t) (mE E) B ρ M K := by
  refine ⟨h.1, h.2.1, fun ι _ k L h1 h2 h3 h4 => ?_⟩
  have hrw : ∀ i : ι, applyOps sz n (L i) (flucDiag sz n u (zt E t) (mE E) (k i))
      = applyOps sz n (L i)
        (minorDiff sz n (qList (L i)) (flucDiagSet sz n u (zt E t) (mE E) (k i))) := by
    intro i
    rw [← flucDiagSet_empty sz n u (zt E t) (mE E) (k i)]
    exact applyOps_eq_applyOps_minorDiff (L i) _
      (fun S => bddMeas_flucDiagSet hE ht u (k i) S)
      (fun S κ hκ => finDepOffRow_flucDiagSet sz n u (zt E t) (mE E) (k i) S hκ)
  simp only [hrw]
  exact h.2.2 ι k L h1 h2 h3 h4

end Env

end MinorExpansion

section MinorGood

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {u : ℝ} {z m : ℂ} {ω : Sizes.SeqΩ sz} {Ψ : ℝ} {M : ℕ}
variable {a b κ : Idx d (sz.L n) (sz.W n)} {S : Finset (Idx d (sz.L n) (sz.W n))}

/-! ### Invertibility of the minors is unconditional -/

/-- **Every minor of `H_u - z` is invertible**, for every sample point and every level, as soon
as `z` is off the real axis. -/
theorem isUnit_det_Hflow_submatrix_sub (sz : Sizes d) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ sz)
    (hz : z.im ≠ 0) (S : Finset (Idx d (sz.L n) (sz.W n))) :
    IsUnit ((Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {x : Idx d (sz.L n) (sz.W n) // x ∉ S} → Idx d (sz.L n) (sz.W n)) Subtype.val
      - z • (1 : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ S}
        {x : Idx d (sz.L n) (sz.W n) // x ∉ S} ℂ)).det :=
  (Matrix.isUnit_iff_isUnit_det _).1
    (RBM.isUnit_sub_smul_of_isHermitian
      ((Sizes.seqHflow_isHermitian sz n u ω).submatrix Subtype.val) hz)

/-! ### (4.9) with the hypotheses it actually needs -/

/-- **(4.9) for the extended entries**, assuming only what one level of the identity uses: the
`S`-minor is invertible and its `κκ` entry does not vanish.  `MinorGoodLe.gEnt_insert` is the
same identity packaged behind `MinorGoodLe`, which asserts both inside the budget; the induction
of `norm_gEnt_le_of_goodEvent` has them at level `S` only. -/
theorem gEnt_insert_of_ne
    (hdet : IsUnit ((Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {x : Idx d (sz.L n) (sz.W n) // x ∉ S} → Idx d (sz.L n) (sz.W n)) Subtype.val
      - z • (1 : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ S}
        {x : Idx d (sz.L n) (sz.W n) // x ∉ S} ℂ)).det)
    (hκ : κ ∉ S) (hne : gEnt sz n u z ω κ κ S ≠ 0)
    (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    gEnt sz n u z ω a b (insert κ S)
      = gEnt sz n u z ω a b S - gEnt sz n u z ω a κ S * gEnt sz n u z ω κ b S
          * (gEnt sz n u z ω κ κ S)⁻¹ := by
  have ha' : a ∉ S := fun h => ha (Finset.mem_insert_of_mem h)
  have hb' : b ∉ S := fun h => hb (Finset.mem_insert_of_mem h)
  have hne' : greenSetMat sz n u z S ω ⟨κ, hκ⟩ ⟨κ, hκ⟩ ≠ 0 := by
    rwa [gEnt_apply hκ hκ] at hne
  rw [gEnt_apply ha hb, gEnt_apply ha' hb', gEnt_apply ha' hκ, gEnt_apply hκ hb',
    gEnt_apply hκ hκ,
    greenSetMat_insert_apply sz n u z S ω hκ hdet hne' ha hb, div_eq_mul_inv, mul_assoc]

/-! ### Level `0` is the full-matrix good event -/

/-- At `S = ∅` the extended entry is the full resolvent entry. -/
theorem gEnt_empty (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ) (ω : Sizes.SeqΩ sz)
    (a b : Idx d (sz.L n) (sz.W n)) :
    gEnt sz n u z ω a b ∅ = green (Sizes.seqHflow sz n u ω) z a b := by
  rw [gEnt_apply (Finset.notMem_empty a) (Finset.notMem_empty b),
    greenSetMat_empty_apply sz n u z ω ⟨a, Finset.notMem_empty a⟩ ⟨b, Finset.notMem_empty b⟩]

/-! ### The simultaneous induction on the level -/

/-- **The recursion `Ψ_{j+1} ≤ Ψ_j + 2 Ψ_j²`, solved**: at every level `S` with
`S.card ≤ M`, the off-diagonal entries and the centered diagonal entries of `G^{(S)}` are at
most `Ψ + 8 |S| Ψ²`.

The two estimates cannot be separated, because the step of (4.9) multiplies by
`(G^{(S)}_{κκ})⁻¹`, whose bound comes from the diagonal estimate at level `S`, while the
diagonal estimate at level `S ∪ {κ}` needs the off-diagonal estimate at level `S`. -/
theorem norm_gEnt_le_of_goodEvent (hz : z.im ≠ 0) (hm : ‖m‖ = 1)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Sizes.seqHflow sz n u ω) z) m Ψ) :
    ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M →
      (∀ a b : Idx d (sz.L n) (sz.W n), a ≠ b →
        ‖gEnt sz n u z ω a b S‖ ≤ Ψ + 8 * (S.card : ℝ) * Ψ ^ 2) ∧
      (∀ a : Idx d (sz.L n) (sz.W n), a ∉ S →
        ‖gEnt sz n u z ω a a S - m‖ ≤ Ψ + 8 * (S.card : ℝ) * Ψ ^ 2) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨fun a b hab => ?_, fun a _ => ?_⟩
      · rw [gEnt_empty]
        simpa using hG.norm_offdiag_le hab
      · rw [gEnt_empty]
        simpa using hG.norm_diag_sub_le a
  | insert κ s hκs ih =>
      intro hcard
      have hscard : s.card ≤ M := by
        rw [Finset.card_insert_of_notMem hκs] at hcard; omega
      obtain ⟨ihoff, ihdiag⟩ := ih hscard
      -- the bound at level `s`
      set B : ℝ := Ψ + 8 * (s.card : ℝ) * Ψ ^ 2 with hB
      have hjM : (s.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hscard
      have h8j : 8 * (s.card : ℝ) * Ψ ≤ 1 := by nlinarith
      have hB0 : 0 ≤ B := by rw [hB]; positivity
      have hB2 : B ≤ 2 * Ψ := by rw [hB]; nlinarith
      -- `|G^{(s)}_{aa}| ≥ 1/2`, hence the bound `2` on the inverse
      have hhalf : ∀ x : Idx d (sz.L n) (sz.W n), x ∉ s → 1 / 2 ≤ ‖gEnt sz n u z ω x x s‖ := by
        intro x hx
        have h1 := ihdiag x hx
        have h2 : ‖m‖ - ‖gEnt sz n u z ω x x s‖ ≤ ‖m - gEnt sz n u z ω x x s‖ :=
          norm_sub_norm_le _ _
        rw [norm_sub_rev, hm] at h2
        linarith
      have hκ0 : gEnt sz n u z ω κ κ s ≠ 0 := by
        intro h0
        have := hhalf κ hκs
        rw [h0, norm_zero] at this
        norm_num at this
      have hinv : ‖(gEnt sz n u z ω κ κ s)⁻¹‖ ≤ 2 := by
        have h := hhalf κ hκs
        rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      -- the arithmetic of one step: `B + 2 B² ≤ Ψ + 8 (|s| + 1) Ψ²`
      have hstep : B + B * B * 2 ≤ Ψ + 8 * ((s.card : ℝ) + 1) * Ψ ^ 2 := by
        rw [hB]; nlinarith [hB0, hB2]
      have hcast : ((insert κ s).card : ℝ) = (s.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hκs]; push_cast; ring
      rw [hcast]
      refine ⟨fun a b hab => ?_, fun a ha => ?_⟩
      · by_cases ha : a ∈ insert κ s
        · rw [gEnt_eq_zero_left ha, norm_zero]
          nlinarith
        by_cases hb : b ∈ insert κ s
        · rw [gEnt_eq_zero_right hb, norm_zero]
          nlinarith
        have haκ : a ≠ κ := fun h => ha (by rw [h]; exact Finset.mem_insert_self κ s)
        have hbκ : b ≠ κ := fun h => hb (by rw [h]; exact Finset.mem_insert_self κ s)
        rw [gEnt_insert_of_ne (isUnit_det_Hflow_submatrix_sub sz n u ω hz s) hκs hκ0 ha hb]
        refine le_trans (norm_sub_le _ _) (le_trans ?_ hstep)
        gcongr ?_ + ?_
        · exact ihoff a b hab
        · rw [norm_mul, norm_mul]
          have h1 := ihoff a κ haκ
          have h2 := ihoff κ b (Ne.symm hbκ)
          have n2 := norm_nonneg (gEnt sz n u z ω κ b s)
          have n3 := norm_nonneg ((gEnt sz n u z ω κ κ s)⁻¹)
          exact mul_le_mul (mul_le_mul h1 h2 n2 hB0) hinv n3 (by positivity)
      · have haκ : a ≠ κ := fun h => ha (by rw [h]; exact Finset.mem_insert_self κ s)
        have ha' : a ∉ s := fun h => ha (Finset.mem_insert_of_mem h)
        rw [gEnt_insert_of_ne (isUnit_det_Hflow_submatrix_sub sz n u ω hz s) hκs hκ0 ha ha]
        have hre : gEnt sz n u z ω a a s
              - gEnt sz n u z ω a κ s * gEnt sz n u z ω κ a s * (gEnt sz n u z ω κ κ s)⁻¹ - m
            = (gEnt sz n u z ω a a s - m)
              - gEnt sz n u z ω a κ s * gEnt sz n u z ω κ a s * (gEnt sz n u z ω κ κ s)⁻¹ := by
          ring
        rw [hre]
        refine le_trans (norm_sub_le _ _) (le_trans ?_ hstep)
        gcongr ?_ + ?_
        · exact ihdiag a ha'
        · rw [norm_mul, norm_mul]
          have h1 := ihoff a κ haκ
          have h2 := ihoff κ a (Ne.symm haκ)
          have n2 := norm_nonneg (gEnt sz n u z ω κ a s)
          have n3 := norm_nonneg ((gEnt sz n u z ω κ κ s)⁻¹)
          exact mul_le_mul (mul_le_mul h1 h2 n2 hB0) hinv n3 (by positivity)

/-! ### The level-budgeted good event -/

/-- **The local law on the good event, at every minor level of size at most `M`.**

The budget is what makes it *producible*: `minorGoodLe_of_goodEvent` derives it, at one fixed
sample point, from the full-matrix good event (4.1) alone.

`det` needs neither the budget nor the good event (`isUnit_det_Hflow_submatrix_sub`), so it is
stated at every level. -/
structure MinorGoodLe (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (ω : Sizes.SeqΩ sz) (Ψ : ℝ) (M : ℕ)
    : Prop where
  /-- Every minor of `H_u - z` is invertible -- unconditional, and at *every* level. -/
  det : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), IsUnit ((Sizes.seqHflow sz n u ω).submatrix
      (Subtype.val : {x : Idx d (sz.L n) (sz.W n) // x ∉ S} → Idx d (sz.L n) (sz.W n)) Subtype.val
      - z • (1 : Matrix {x : Idx d (sz.L n) (sz.W n) // x ∉ S}
        {x : Idx d (sz.L n) (sz.W n) // x ∉ S} ℂ)).det
  /-- The diagonal entries of the budgeted minors are non-zero. -/
  diag_ne : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M → ∀ a : Idx d (sz.L n) (sz.W n),
    a ∉ S → gEnt sz n u z ω a a S ≠ 0
  /-- `|G^{(S)}_{aa}|⁻¹ ≤ 2` for `|S| ≤ M` -- the quantitative form of (4.1). -/
  inv_le : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M → ∀ a : Idx d (sz.L n) (sz.W n),
    ‖(gEnt sz n u z ω a a S)⁻¹‖ ≤ 2
  /-- `|G^{(S)}_{ab}| ≤ Ψ` for `a ≠ b` and `|S| ≤ M` -- (4.2). -/
  off_le : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M → ∀ a b : Idx d (sz.L n) (sz.W n),
    a ≠ b → ‖gEnt sz n u z ω a b S‖ ≤ Ψ
  /-- `|G^{(S)}_{aa} - m| ≤ Ψ` for `|S| ≤ M` -- (4.3). -/
  diag_sub_le : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M → ∀ a : Idx d (sz.L n) (sz.W n),
    a ∉ S → ‖gEnt sz n u z ω a a S - m‖ ≤ Ψ

/-- **(4.9) inside the budget.**  The identity is available at `S ∪ {κ}` as soon as `S` itself
is within the budget; the estimate of the right-hand side then uses the fields at level `S`. -/
theorem MinorGoodLe.gEnt_insert (hg : MinorGoodLe sz n u z m ω Ψ M) (hS : S.card ≤ M)
    (hκ : κ ∉ S) (ha : a ∉ insert κ S) (hb : b ∉ insert κ S) :
    gEnt sz n u z ω a b (insert κ S)
      = gEnt sz n u z ω a b S - gEnt sz n u z ω a κ S * gEnt sz n u z ω κ b S
          * (gEnt sz n u z ω κ κ S)⁻¹ :=
  gEnt_insert_of_ne (hg.det S) hκ (hg.diag_ne S hS κ hκ) ha hb

/-- **The level-budgeted good event follows from (4.1) at the same sample point**, with the
threshold degraded from `Ψ` to `2Ψ`.

This is a pointwise implication: `ω` occurs only as the point at which the hypothesis and the
conclusion are both read.  Nothing is assumed for all `ω`. -/
theorem minorGoodLe_of_goodEvent (hz : z.im ≠ 0) (hm : ‖m‖ = 1)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Sizes.seqHflow sz n u ω) z) m Ψ) :
    MinorGoodLe sz n u z m ω (2 * Ψ) M := by
  classical
  have key := norm_gEnt_le_of_goodEvent hz hm hΨ0 hΨ4 hMΨ hG
  -- the invariant collapses to `2Ψ` inside the budget
  have hle : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M →
      Ψ + 8 * (S.card : ℝ) * Ψ ^ 2 ≤ 2 * Ψ := by
    intro S hS
    have hjM : ((S.card : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hS
    nlinarith
  have hdiag : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M → ∀ a : Idx d (sz.L n) (sz.W n),
      a ∉ S → ‖gEnt sz n u z ω a a S - m‖ ≤ 2 * Ψ :=
    fun S hS a ha => le_trans ((key S hS).2 a ha) (hle S hS)
  have hhalf : ∀ S : Finset (Idx d (sz.L n) (sz.W n)), S.card ≤ M → ∀ a : Idx d (sz.L n) (sz.W n),
      a ∉ S → 1 / 2 ≤ ‖gEnt sz n u z ω a a S‖ := by
    intro S hS a ha
    have h1 := hdiag S hS a ha
    have h2 : ‖m‖ - ‖gEnt sz n u z ω a a S‖ ≤ ‖m - gEnt sz n u z ω a a S‖ := norm_sub_norm_le _ _
    rw [norm_sub_rev, hm] at h2
    linarith
  refine
    { det := isUnit_det_Hflow_submatrix_sub sz n u ω hz
      diag_ne := ?_
      inv_le := ?_
      off_le := fun S hS a b hab => le_trans ((key S hS).1 a b hab) (hle S hS)
      diag_sub_le := hdiag }
  · intro S hS a ha h0
    have := hhalf S hS a ha
    rw [h0, norm_zero] at this
    norm_num at this
  · intro S hS a
    by_cases ha : a ∉ S
    · have h := hhalf S hS a ha
      rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    · rw [gEnt_eq_zero_left (not_not.1 ha), _root_.inv_zero, norm_zero]
      norm_num

/-- The shape in which the flow consumes it: `z = z_u`, `m = m_E`, where `|m_E| = 1` is
`norm_mE`. -/
theorem minorGoodLe_of_goodEvent_flow {E : ℝ} (hE : |E| ≤ 2) (hz : (zt E u).im ≠ 0)
    (hΨ0 : 0 ≤ Ψ) (hΨ4 : Ψ ≤ 1 / 4) (hMΨ : 8 * M * Ψ ≤ 1)
    (hG : GoodEvent (green (Sizes.seqHflow sz n u ω) (zt E u)) (mE E) Ψ) :
    MinorGoodLe sz n u (zt E u) (mE E) ω (2 * Ψ) M :=
  minorGoodLe_of_goodEvent hz (norm_mE hE) hΨ0 hΨ4 hMΨ hG

end MinorGood

/-! ### Compiled nonempty instances at `d = 3`, `L = 3`, `W = 2`, `lam = 1/2`

`RBM.Green.MinorGoodLeInst.szH` is the constant size sequence `d = 3`, `L n = 3`, `W n = 2`,
`lam n = 1/2` (no limit statement is claimed at it), at the slice `n = 0`: `N = (W L)^3 = 216`
sites, `W^d = 8`.

* **Target 1** `flucGainUpTo'_of_minorDiffGainUpTo'` at `E = 0`, `t = 0` (`|E| < 2`, `t < 1`:
  `η = Im z_0 = 1`, so `‖Z^{(S)}_k‖ ≤ 2 (η⁻¹ + 1) = 4` at every level `S`), any real `u`.  A word
  of `q` letters `Q` costs `2^q` (`norm_applyOps_le`), the `q`-fold difference costs `2^q`
  (`norm_minorDiff_le`): `4^q · 4 ≤ B ρ^q` for `q ≤ M = 2` at `(B, ρ, M, K) = (64, 1, 2, 2)` (tight
  at `q = 2`).  So `MinorDiffGainUpTo'` holds gain-free at these constants without any local law
  (the gain `ρ^q` for `q ≥ 1` is S1-25's content, not claimed), and the theorem applies to it; the
  consequence is applied at one slot `ι = Fin 1`, the row `(0,0,0)`, with the word
  `Q_{(0,0,1)} Q_{(0,1,0)}` (two letters `Q`, distinct rows, different from the row of the slot).
  The two lemmas that conclude `MinorDiffGainUpTo'` and `FlucGainUpTo'` are private (or
  `example`s): a public theorem concluding a premise would hide it from the premise scan.
* **Target 2** `minorGoodLe_of_goodEvent_flow` at `E = 0`, `u = 1/16`, `ω = 0`, `Ψ = 1/8`, `M = 1`:
  `ω = 0` gives `H_u = 0`, `G = -(z_u)⁻¹ 1`, with `z_u = (15/16) i`, `G = (16/15) i 1`,
  `‖G - m 1‖_max = 1/15 ≤ Ψ` (so (4.1) holds at `ω`); `Ψ ≤ 1/4` and `8 M Ψ = 1` (the boundary of
  the level budget).  The conclusion is not trivial there: `inv_le` says
  `‖(G^{(S)}_{aa})⁻¹‖ = 15/16 ≤ 2` and the level-`0` entry is `G_{aa} = (16/15) i ≠ m`.
There is no external hypothesis. -/

namespace MinorGoodLeInst

noncomputable section

/-- The sizes `d = 3`, `L = 3`, `W = 2`, `lam = 1/2` (constant sequences). -/
private def szH : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

/-- Four sites of the fine lattice `Z_6^3`. -/
private def siteA : Idx 3 (szH.L 0) (szH.W 0) := ![0, 0, 0]
private def siteB : Idx 3 (szH.L 0) (szH.W 0) := ![0, 0, 1]
private def siteC : Idx 3 (szH.L 0) (szH.W 0) := ![0, 1, 0]
private def siteD : Idx 3 (szH.L 0) (szH.W 0) := ![1, 0, 0]

private theorem siteB_ne_siteA : siteB ≠ siteA := by decide
private theorem siteC_ne_siteA : siteC ≠ siteA := by decide
private theorem siteB_ne_siteC : siteB ≠ siteC := by decide
private theorem siteD_ne_siteA : siteD ≠ siteA := by decide

private theorem hE0 : |(0 : ℝ)| < 2 := by norm_num

/-- `η = Im z_0 = 1` at `E = 0`, `t = 0`. -/
private theorem eta_zero : (zt 0 0).im = 1 := by
  rw [zt_im, mE_im, show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The integral of a product of nonnegative slot factors, slot `i` bounded by `B ρ^{q i}`. -/
private theorem integral_prod_le {ι : Type*} [Fintype ι]
    {f : ι → Sizes.SeqΩ szH → ℝ} {B ρ : ℝ} {q : ι → ℕ}
    (hf : ∀ i ω, 0 ≤ f i ω) (hpt : ∀ i ω, f i ω ≤ B * ρ ^ q i) :
    ∫ ω, ∏ i, f i ω ∂(Sizes.seqP szH) ≤ B ^ Fintype.card ι * ρ ^ ∑ i, q i := by
  have hpt' : ∀ ω : Sizes.SeqΩ szH, ∏ i, f i ω ≤ B ^ Fintype.card ι * ρ ^ ∑ i, q i := by
    intro ω
    calc ∏ i, f i ω ≤ ∏ i, (B * ρ ^ q i) :=
          Finset.prod_le_prod₀ (fun i _ => hf i ω) fun i _ => hpt i ω
      _ = B ^ Fintype.card ι * ρ ^ ∑ i, q i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
            Finset.prod_pow_eq_pow_sum]
  calc ∫ ω, ∏ i, f i ω ∂(Sizes.seqP szH)
      ≤ ∫ _ω, B ^ Fintype.card ι * ρ ^ ∑ i, q i ∂(Sizes.seqP szH) :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => Finset.prod_nonneg fun i _ => hf i ω)
          (integrable_const _) (Filter.Eventually.of_forall hpt')
    _ = B ^ Fintype.card ι * ρ ^ ∑ i, q i := by simp

/-- **`MinorDiffGainUpTo'` holds gain-free.**  If `2^q · 2^q · 2 (η⁻¹ + 1) ≤ B ρ^q` for every
`q ≤ M`, then `MinorDiffGainUpTo'` holds at `(B, ρ, M, K)` for every `K`, by `norm_minorDiff_le`,
`norm_flucDiagSet_le_env` and `norm_applyOps_le`.  Private: see the header. -/
private theorem minorDiffGainUpTo'_of_crude {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (u : ℝ) {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ) {M K : ℕ}
    (hcrude : ∀ q ≤ M, 2 ^ q * (2 ^ q * (2 * (((zt E t).im)⁻¹ + 1))) ≤ B * ρ ^ q) :
    MinorDiffGainUpTo' szH 0 u (zt E t) (mE E) B ρ M K := by
  refine ⟨hB, hρ, fun ι _ k L _ _ hlen _ => ?_⟩
  refine integral_prod_le (q := fun i => numQ (L i))
    (fun i ω => norm_nonneg _) fun i ω => ?_
  have hmd : ∀ ω' : Sizes.SeqΩ szH,
      ‖minorDiff szH 0 (qList (L i))
        (flucDiagSet szH 0 u (zt E t) (mE E) (k i)) ω'‖
        ≤ 2 ^ numQ (L i) * (2 * (((zt E t).im)⁻¹ + 1)) := by
    intro ω'
    have := norm_minorDiff_le (qList (L i))
      (flucDiagSet szH 0 u (zt E t) (mE E) (k i))
      (b := 2 * (((zt E t).im)⁻¹ + 1))
      (fun S ω'' => norm_flucDiagSet_le_env hE ht u (k i) S ω'') ω'
    rwa [length_qList] at this
  refine le_trans (norm_applyOps_le (L i) hmd ω) ?_
  exact hcrude _ (le_trans List.countP_le_length (hlen i))

/-- `MinorDiffGainUpTo'` at `(B, ρ, M, K) = (64, 1, 2, 2)`, `E = t = 0`: gain-free (tight at
`q = 2`). -/
private theorem minorDiffGain_szH (u : ℝ) :
    MinorDiffGainUpTo' szH 0 u (zt 0 0) (mE 0) 64 1 2 2 :=
  minorDiffGainUpTo'_of_crude (E := 0) (t := 0) hE0 (by norm_num) u
    (by norm_num) (by norm_num) fun q hq => by
      rw [eta_zero]
      interval_cases q <;> norm_num

/-- **Instance of `flucGainUpTo'_of_minorDiffGainUpTo'`** (target 1): `d = 3`, `L = 3`, `W = 2`,
`E = t = 0`, `(B, ρ, M, K) = (64, 1, 2, 2)`, every deterministic hypothesis (`|E| < 2`, `t < 1`,
`MinorDiffGainUpTo'`) discharged.  An `example`, so that no public theorem concludes
`FlucGainUpTo'` at these data. -/
example (u : ℝ) : FlucGainUpTo' szH 0 u (zt 0 0) (mE 0) 64 1 2 2 :=
  flucGainUpTo'_of_minorDiffGainUpTo' (E := 0) (t := 0) hE0 (by norm_num) u (minorDiffGain_szH u)

/-- The single slot `ι = Fin 1` of the check, at the row `k = (0, 0, 0)`. -/
private def slotK : Fin 1 → Idx 3 (szH.L 0) (szH.W 0) := fun _ => siteA

/-- The word `Q_{(0,0,1)} Q_{(0,1,0)}`: two letters `Q`, distinct rows, both different from the row
`(0, 0, 0)` of the slot. -/
private def slotWord : Fin 1 → List (Bool × Idx 3 (szH.L 0) (szH.W 0)) :=
  fun _ => [(true, siteB), (true, siteC)]

/-- **Instance of the conclusion of target 1 at the top of the budget**: the side conditions of
`FlucGainUpTo'` (`Nodup` rows, rows different from the slot's, `length ≤ M`, `#ι ≤ K`) hold
jointly at one slot with a word of `numQ = 2 = M` letters `Q`, and the conclusion reads
`∫ ‖applyOps L Z_k‖ ≤ 64^1 · 1^2`. -/
theorem inst_flucGain_word (u : ℝ) :
    ∫ ω, ∏ i : Fin 1, ‖applyOps szH 0 (slotWord i)
        (flucDiag szH 0 u (zt 0 0) (mE 0) (slotK i)) ω‖ ∂(Sizes.seqP szH)
      ≤ 64 ^ Fintype.card (Fin 1) * 1 ^ ∑ i : Fin 1, numQ (slotWord i) :=
  (flucGainUpTo'_of_minorDiffGainUpTo' (E := 0) (t := 0) hE0 (by norm_num) u
    (minorDiffGain_szH u)).gain (Fin 1) slotK slotWord
    (fun i => by simp [slotWord, siteB_ne_siteC])
    (fun i x hx => by
      simp only [slotWord, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact siteB_ne_siteA
      · exact siteC_ne_siteA)
    (fun i => by simp [slotWord]) (by simp)

/-- The word `Q_{(0,0,1)} P_{(0,1,0)} Q_{(1,0,0)}` of the annihilation check. -/
private def word3 : List (Bool × Idx 3 (szH.L 0) (szH.W 0)) :=
  [(true, siteB), (false, siteC), (true, siteD)]

/-- **Instance of `applyOps_eq_applyOps_minorDiff`** (the annihilation identity): at `d = 3`,
`L = 3`, `W = 2`, `E = t = 0`, the word `Q_{(0,0,1)} P_{(0,1,0)} Q_{(1,0,0)}` (two `Q`, one `P`)
applied to `Z_{(0,0,0)}` equals the same word applied to the second difference
`Δ_{(0,0,1)} Δ_{(1,0,0)} Z^{(·)}_{(0,0,0)}`; the hypotheses `hbdd`, `hind` are discharged by
`bddMeas_flucDiagSet` and `finDepOffRow_flucDiagSet`. -/
theorem inst_annihilation (u : ℝ) :
    applyOps szH 0 word3 (flucDiag szH 0 u (zt 0 0) (mE 0) siteA)
      = applyOps szH 0 word3
        (minorDiff szH 0 (qList word3) (flucDiagSet szH 0 u (zt 0 0) (mE 0) siteA)) := by
  rw [← flucDiagSet_empty szH 0 u (zt 0 0) (mE 0) siteA]
  exact applyOps_eq_applyOps_minorDiff word3 _
    (fun S => bddMeas_flucDiagSet (E := 0) (t := 0) hE0 (by norm_num) u _ S)
    (fun S κ hκ => finDepOffRow_flucDiagSet szH 0 u (zt 0 0) (mE 0) siteA S hκ)

/-- The difference of the annihilation check is a genuine second difference: `qList word3` is the
two rows carrying a `Q`. -/
theorem inst_qList : qList word3 = [siteB, siteD] := rfl

/-- **Instance of `finDepOffRows_of_minorSet`** (through `finDepOffRows_greenSetMat`): the minor
resolvent on the complement of the two rows `(0,0,0)`, `(0,0,1)` is strictly independent of both. -/
theorem inst_finDepOffRows (u : ℝ) :
    FinDepOffRows szH 0 ({siteA, siteB} : Finset _)
      (greenSetMat szH 0 u (zt 0 (1 / 16)) {siteA, siteB}) :=
  finDepOffRows_greenSetMat _ _ _ _ _

/-! #### The sample point `ω = 0` -/

/-- The sample point `ω = 0` has `H_u = 0` at every `u`. -/
private theorem seqHflow_zero_omega (u : ℝ) :
    Sizes.seqHflow szH 0 u (0 : Sizes.SeqΩ szH) = 0 := by
  rw [Sizes.seqHflow_eq_smul]
  have h : Sizes.seqXmat szH 0 (0 : Sizes.SeqΩ szH) = 0 := by
    ext i j
    simp [Sizes.seqXmat, Xmat, Xentry, Sizes.slice]
  rw [h, smul_zero]

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `m^{(0)} = i`. -/
private theorem mE_zero : mE 0 = Complex.I := by
  apply Complex.ext <;> simp [mE, sqrt_four]

/-- `z_u = zt 0 (1/16) = (15/16) i`. -/
private theorem zt_sixteenth : zt 0 (1 / 16) = (15 / 16 : ℂ) * Complex.I := by
  simp only [zt, mE_zero]
  push_cast
  ring

/-- `G = (0 - z)⁻¹ = (-z)⁻¹ • 1`. -/
private theorem green_zero {ν : Type*} [Fintype ν] [DecidableEq ν] {z : ℂ} (hz : z ≠ 0) :
    green (0 : Matrix ν ν ℂ) z = (-z)⁻¹ • (1 : Matrix ν ν ℂ) := by
  unfold green
  refine Matrix.inv_eq_right_inv ?_
  simp [smul_smul, inv_mul_cancel₀ hz]

/-- `(-z_u)⁻¹ = (16/15) i`. -/
private theorem inv_neg_zt : (-(zt 0 (1 / 16)))⁻¹ = (16 / 15 : ℂ) * Complex.I := by
  rw [zt_sixteenth]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  simp

private theorem zt_ne_zero : zt 0 (1 / 16) ≠ 0 := by
  rw [zt_sixteenth]
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero

/-- `‖(16/15) i - i‖ = 1/15`. -/
private theorem norm_diag_sub : ‖(16 / 15 : ℂ) * Complex.I - Complex.I‖ = 1 / 15 := by
  have : (16 / 15 : ℂ) * Complex.I - Complex.I = ((1 / 15 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  norm_num

/-- (4.1) at `ω = 0`, `u = 1/16`, `E = 0`, `Ψ = 1/8`: `G = (16/15) i 1`, `m = i`,
`‖G - m 1‖_max = 1/15 ≤ 1/8`. -/
private theorem goodEvent_omega_zero :
    GoodEvent (green (Sizes.seqHflow szH 0 (1 / 16) (0 : Sizes.SeqΩ szH)) (zt 0 (1 / 16)))
      (mE 0) (1 / 8) := by
  rw [seqHflow_zero_omega, green_zero zt_ne_zero, inv_neg_zt, mE_zero]
  intro x y
  by_cases h : x = y
  · subst h
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, ite_true, smul_eq_mul, mul_one]
    rw [norm_diag_sub]
    norm_num
  · simp [h]

/-- `Im z_u ≠ 0`. -/
private theorem zt_im_ne : (zt 0 (1 / 16)).im ≠ 0 := by
  rw [zt_sixteenth]
  simp

/-- **Instance of `minorGoodLe_of_goodEvent_flow`** (target 2): `d = 3`, `L = 3`, `W = 2`,
`E = 0`, `u = 1/16`, `ω = 0`, `M = 1`, `Ψ = 1/8`; every hypothesis is proved (`|E| ≤ 2`,
`Im z_u ≠ 0`, `0 ≤ 1/8`, `1/8 ≤ 1/4`, `8 · 1 · 1/8 ≤ 1`, and (4.1) at `ω = 0`). -/
theorem inst_minorGoodLe_flow :
    MinorGoodLe szH 0 (1 / 16) (zt 0 (1 / 16)) (mE 0) 0 (2 * (1 / 8)) 1 :=
  minorGoodLe_of_goodEvent_flow (E := 0) (by norm_num) zt_im_ne (by norm_num) (by norm_num)
    (by norm_num) goodEvent_omega_zero

/-- **Instance of `minorGoodLe_of_goodEvent`** (the general-`z`, general-`m` form), at
`z = (15/16) i`, `m = i`: the same data, `‖m‖ = 1` and `Im z ≠ 0` stated for the explicit numbers. -/
theorem inst_minorGoodLe_general :
    MinorGoodLe szH 0 (1 / 16) ((15 / 16 : ℂ) * Complex.I) Complex.I 0 (2 * (1 / 8)) 1 := by
  have h := inst_minorGoodLe_flow
  rw [zt_sixteenth, mE_zero] at h
  exact h

/-- **Instance of `isUnit_det_Hflow_submatrix_sub`**: the minor on the complement of `{(0,0,0)}` at
`ω = 0`, `u = 1/16`, `z = z_u` is invertible. -/
theorem inst_isUnit_det :
    IsUnit ((Sizes.seqHflow szH 0 (1 / 16) 0).submatrix
      (Subtype.val : {x : Idx 3 (szH.L 0) (szH.W 0) // x ∉ ({siteA} : Finset _)} →
        Idx 3 (szH.L 0) (szH.W 0)) Subtype.val
      - zt 0 (1 / 16) • (1 : Matrix {x : Idx 3 (szH.L 0) (szH.W 0) // x ∉ ({siteA} : Finset _)}
        {x : Idx 3 (szH.L 0) (szH.W 0) // x ∉ ({siteA} : Finset _)} ℂ)).det :=
  isUnit_det_Hflow_submatrix_sub szH 0 (1 / 16) 0 zt_im_ne {siteA}

/-- **Instance of `norm_gEnt_le_of_goodEvent`**: the simultaneous induction at the point of
`inst_minorGoodLe_flow`; at the levels `|S| ≤ 1` the entries are within `Ψ + 8 |S| Ψ²`
(`= 1/4` at `|S| = 1`). -/
theorem inst_norm_gEnt :
    ∀ S : Finset (Idx 3 (szH.L 0) (szH.W 0)), S.card ≤ 1 →
      (∀ a b, a ≠ b → ‖gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 a b S‖
        ≤ 1 / 8 + 8 * (S.card : ℝ) * (1 / 8) ^ 2) ∧
      (∀ a, a ∉ S → ‖gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 a a S - mE 0‖
        ≤ 1 / 8 + 8 * (S.card : ℝ) * (1 / 8) ^ 2) :=
  norm_gEnt_le_of_goodEvent (M := 1) zt_im_ne (norm_mE (by norm_num)) (by norm_num)
    (by norm_num) (by norm_num) goodEvent_omega_zero

/-- **Instance of `MinorGoodLe.gEnt_insert`** (hence `gEnt_insert_of_ne`): (4.9) inside the budget,
`S = ∅`, `κ = (0,0,0)`, `a = (0,0,1)`, `b = (0,1,0)`. -/
theorem inst_gEnt_insert :
    gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 siteB siteC (insert siteA ∅)
      = gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 siteB siteC ∅
        - gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 siteB siteA ∅
          * gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 siteA siteC ∅
          * (gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 siteA siteA ∅)⁻¹ :=
  inst_minorGoodLe_flow.gEnt_insert (S := ∅) (by simp) (by simp) (by decide) (by decide)

/-- **Instance of the field `inv_le` of `MinorGoodLe`**: `‖(G^{(S)}_{aa})⁻¹‖ ≤ 2` at
`S = {(0,0,0)}` (`|S| = 1 = M`), `a = (0,0,1)`. -/
theorem inst_level_one :
    ‖(gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 siteB siteB {siteA})⁻¹‖ ≤ 2 :=
  inst_minorGoodLe_flow.inv_le {siteA} (by simp) siteB

/-- **Instance of `gEnt_empty`**: at level `∅` the extended entry is the full resolvent entry, here
the diagonal entry `(0,0,1)` of `G = (16/15) i 1`, which is `(16/15) i`, not `m = i`. -/
theorem inst_gEnt_empty :
    gEnt szH 0 (1 / 16) (zt 0 (1 / 16)) 0 siteB siteB ∅ = (16 / 15 : ℂ) * Complex.I := by
  rw [gEnt_empty, seqHflow_zero_omega, green_zero zt_ne_zero, inv_neg_zt]
  simp

end

end MinorGoodLeInst

end RBM.Green
