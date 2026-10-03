/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import RBM3D.Gauss.FlowCalculus
import RBM3D.Green.EntryCore
import RBM3D.Green.EntryDom
import RBM3D.Green.LDEQuad
import RBM3D.Green.RowIndep
import RBM3D.Hierarchy.ContractionBasic

/-!
# Row conditioning, differentiability of the resolvent, and the base layer of fluctuation
averaging, `d ≥ 3` (S1-17)

Ticket T2061.  Port of `RBM2D/Green/CondRow.lean`, `RBM2D/Green/GreenDeriv.lean` and
`RBM2D/Green/FlucVanish.lean` at commit `c9a24cf` (492, 418 and 556 lines; the kept parts of
`0c1330a`: 373, 356 and 477) to the fine lattice `Z_{WL}^d`, with the renaming rules R1-R4 of
`docs/tickets/ST1-COMMON.md` (item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L`/`Idx L W`
become `Zd d L`/`Idx d L W`, `W²`/`W⁻²` become `W^d`/`(W^d)⁻¹`, the block fibre is `Fin (W^d)`,
and `Coord`, `svar` become `CoordF`, `svarF d L W g`.  The paper (arXiv:2507.20274) does not
state these lemmas: `paper/tex/3_5_Loop_Hierarchy.tex:37` says that the estimates of `lem_GbEXP`
(among them `(GavLGEX)`, `3_5:33`) have been proven as Lemma 4.1 of `[YY_25]` for 1D random band
matrices and that their proofs are dimension-independent (resolvent identities and large deviation
estimates); the mathematics is `E_x = E[· | H^{(x)}]` with `G^{(x)}` a function of the entries
outside row and column `x`.

## Contents

* CondRow (`RBM2D/Green/CondRow.lean`): `IsRowCoord`, `rowSplit`, `measurePreserving_rowSplit`,
  `condRow` (`E_k` as the integral over the row-`k` coordinates, the others frozen),
  `condRow_condRow`, `condRow_sub_condRow`, `integral_condRow`, `FinDepOffRow`,
  `finDepOffRow_of_minor`, `greenMinorMat`, `greenMinorMat_eq_minorGreen` (the minor `G^{(k)}` of
  (4.9) is the row-conditioned object).  The row block `rowSet`, `offRowCoord` and the minor's
  dependence `Hflow_submatrix_congr_offRowCoord` are those of `Green/RowIndep.lean` (T2038); the
  minor formula `inv_minor_resolvent` is that of `Green/EntryCore.lean`.
* GreenDeriv (`RBM2D/Green/GreenDeriv.lean`): the coordinate directions `Bmat`, `Xmat_eq_sum`, the
  Hermitian projection `hermCLM`, the extended resolvent `resH`, `hasFDerivAt_resH`,
  `finDep_of_Hflow` and `continuous_green_comp` (continuity of `t ↦ G_t`).  `usedCoords` is the
  merged one of `Hierarchy/ContractionBasic.lean` (T2032); `continuous_green_comp` is
  `RBM.Gauss.continuous_green_of_isHermitian` (`Gauss/FlowCalculus.lean`, T2030) read through
  `Gres H z true = green H z`.
* FlucVanish (`RBM2D/Green/FlucVanish.lean`): closure properties of `FinDepOffRow`, the
  vanishing lemma `integral_mul_prod_eq_zero`, the fluctuations `flucDiag`, `flucDiagMinor` and
  their bounds, the conjugation pattern `epsHom`, `flucAvg`, the weights `UniformWeight`,
  `uniformWeight_blockAvg2` (the block average `W^{-d} 1(k ∈ 𝓘_a)`), and
  `flucVanish_blockAvg2_eq_blkCoef2` (it is `blkCoef2` of `Green/EntryDom.lean`, T2057, read
  through `splitEquiv`).

## Differences from RBM2D (residual, after the renaming)

* **`uniformWeight_svar` is false at `d ≥ 3` as ported** (DECISIONS §30, Amend 1 of T2061; paper
  delta candidate `T2061a`).  RBM2D's `svar` is a fixed uniform five-point profile; `svarF d L W g`
  carries the coupling `g` and takes the two nonzero values `W^{-d}(1 + 2dg²)⁻¹` and
  `g² W^{-d}(1 + 2dg²)⁻¹` on its support, so the row is uniform only at `g² = 1`
  (`not_uniformWeight_svarF` compiles the negative statement).  `UniformWeight` is kept (the block
  average is uniform at every `d`); the new `BoundedWeight` (`0 ≤ t ≤ c` on `A`, `0` off `A`,
  `∑ t ≤ 1`), `UniformWeight.toBoundedWeight` and `boundedWeight_svarF` (`c = W^{-d}`,
  `#A = (2d + 1) W^d`) replace it.  RBM2D's `UniformWeight.mass : c · #A ≤ 1` is not available
  for the row (`c · #A = 2d + 1`), so `BoundedWeight` carries the bound `∑ t ≤ 1` instead.
* The five-point support `sbSupport L` is `flucVanish_sbSupport d L = {0} ∪ {x : |x|₁ = 1}`
  (`2d + 1` points for `3 ≤ L`); `flucVanish_card_sbSupport_le` (`≤ 5`) is replaced by
  `flucVanish_card_sbSupport` (`= 2d + 1`, needs `3 ≤ L`), and the support counts are
  `flucVanish_card_svarSupport_eq` (`(2d + 1) W^d` for `3 ≤ L`) and `flucVanish_card_blockSupport`
  (`W^d`).  The row support is oriented `b_j - b_i` (DECISIONS §30).
* The private `Checks` sections of the three RBM2D files are replaced by the instances
  `RBM.Green.FlucVanishInst.*` at the end of this file (`sz0` of `Defs/Sizes.lean`, and the sizes
  `szS` for the lemmas that name `IsRowCoord`).
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

/-! ### The row-`k` coordinates -/

/-- The coordinate `c` belongs to **row `k` at slice `n`**. -/
def IsRowCoord {d : ℕ} (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (c : Sizes.SeqCoord sz) : Prop :=
  c ∈ rowSet sz n k

instance decidableIsRowCoord {d : ℕ} (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) :
    DecidablePred (IsRowCoord sz n k) := fun c => by
  unfold IsRowCoord; infer_instance

@[simp] theorem isRowCoord_mk {d : ℕ} (sz : Sizes d) (n : ℕ) (k i j : Idx d (sz.L n) (sz.W n))
    (b : Bool) :
    IsRowCoord sz n k (⟨n, i, j, b⟩ : Sizes.SeqCoord sz) ↔ (i = k ∨ j = k) :=
  mem_rowSet

section CondRow

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

noncomputable def rowSplit {d : ℕ} (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (ω ω' : Sizes.SeqΩ sz) : Sizes.SeqΩ sz :=
  fun c => if IsRowCoord sz n k c then ω' c else ω c

theorem rowSplit_apply_of_isRowCoord (k : Idx d (sz.L n) (sz.W n)) (ω ω' : Sizes.SeqΩ sz)
    {c : Sizes.SeqCoord sz}
    (hc : IsRowCoord sz n k c) : rowSplit sz n k ω ω' c = ω' c :=
  ite_eq_left hc

theorem rowSplit_apply_of_not_isRowCoord (k : Idx d (sz.L n) (sz.W n)) (ω ω' : Sizes.SeqΩ sz)
    {c : Sizes.SeqCoord sz}
    (hc : ¬ IsRowCoord sz n k c) : rowSplit sz n k ω ω' c = ω c :=
  ite_eq_right hc

@[simp] theorem rowSplit_rowSplit (k : Idx d (sz.L n) (sz.W n)) (ω ω' ω'' : Sizes.SeqΩ sz) :
    rowSplit sz n k (rowSplit sz n k ω ω') ω'' = rowSplit sz n k ω ω'' := by
  funext c
  unfold rowSplit
  split_ifs <;> rfl

theorem measurable_rowSplit (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) :
    Measurable fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2 := by
  refine measurable_pi_iff.2 fun c => ?_
  by_cases hc : IsRowCoord sz n k c
  · have h : (fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2 c)
        = fun p => p.2 c := by
      funext p; exact rowSplit_apply_of_isRowCoord k p.1 p.2 hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_snd
  · have h : (fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2 c)
        = fun p => p.1 c := by
      funext p; exact rowSplit_apply_of_not_isRowCoord k p.1 p.2 hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_fst

theorem preimage_rowSplit_pi (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (s : Finset (Sizes.SeqCoord sz))
    (t : Sizes.SeqCoord sz → Set ℝ) :
    (fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2) ⁻¹'
        ((s : Set (Sizes.SeqCoord sz)).pi t)
      = ((↑(s.filter fun c => ¬ IsRowCoord sz n k c) : Set (Sizes.SeqCoord sz)).pi t)
        ×ˢ ((↑(s.filter fun c => IsRowCoord sz n k c) : Set (Sizes.SeqCoord sz)).pi t) := by
  ext ⟨ω, ω'⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c hc.1
      rwa [rowSplit_apply_of_not_isRowCoord k ω ω' hc.2] at this
    · have := h c hc.1
      rwa [rowSplit_apply_of_isRowCoord k ω ω' hc.2] at this
  · rintro ⟨h1, h2⟩ c hc
    by_cases hcr : IsRowCoord sz n k c
    · rw [rowSplit_apply_of_isRowCoord k ω ω' hcr]; exact h2 c ⟨hc, hcr⟩
    · rw [rowSplit_apply_of_not_isRowCoord k ω ω' hcr]; exact h1 c ⟨hc, hcr⟩

theorem measurePreserving_rowSplit (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) :
    MeasurePreserving (fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2)
      ((Sizes.seqP sz).prod (Sizes.seqP sz)) (Sizes.seqP sz) := by
  refine ⟨measurable_rowSplit sz n k, ?_⟩
  have hmeas := measurable_rowSplit sz n k
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    preimage_rowSplit_pi sz n k s t, Measure.prod_prod]
  show Sizes.seqP sz _ * Sizes.seqP sz _ = _
  rw [Sizes.seqP, Measure.infinitePi_pi _ fun i _ => ht i,
    Measure.infinitePi_pi _ fun i _ => ht i,
    mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not s (IsRowCoord sz n k) _

/-! ### The conditional expectation -/

/-- **`E_k[X] = E[X | H^{(k)}]`**, realized as the integral over the row-`k` coordinates with
all the other coordinates frozen (exact Fubini in the product model, not an abstract
`MeasureTheory.condExp`; every identity below is pointwise in `ω`). -/
noncomputable def condRow {d : ℕ} (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (X : Sizes.SeqΩ sz → ℂ) : Sizes.SeqΩ sz → ℂ :=
  fun ω => ∫ ω', X (rowSplit sz n k ω ω') ∂(Sizes.seqP sz)

theorem condRow_apply (k : Idx d (sz.L n) (sz.W n)) (X : Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) :
    condRow sz n k X ω = ∫ ω', X (rowSplit sz n k ω ω') ∂(Sizes.seqP sz) := rfl

/-- `ω' ↦ X (rowSplit k ω ω')` is integrable for **every** frozen `ω`. -/
def RowIntegrable {d : ℕ} (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (X : Sizes.SeqΩ sz → ℂ) : Prop :=
  ∀ ω : Sizes.SeqΩ sz, Integrable (fun ω' => X (rowSplit sz n k ω ω')) (Sizes.seqP sz)

theorem measurable_rowSplit_right (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) :
    Measurable fun ω' : Sizes.SeqΩ sz => rowSplit sz n k ω ω' :=
  (measurable_rowSplit sz n k).comp (measurable_const.prodMk measurable_id)

theorem rowIntegrable_of_measurable_of_bound {k : Idx d (sz.L n) (sz.W n)}
    {X : Sizes.SeqΩ sz → ℂ} (hX : Measurable X)
    {C : ℝ} (hC : ∀ ω, ‖X ω‖ ≤ C) : RowIntegrable sz n k X := fun ω =>
  Integrable.mono' (integrable_const C)
    ((hX.comp (measurable_rowSplit_right sz n k ω)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => hC _)

/-! #### Idempotence and the projection identity -/

@[simp] theorem condRow_const (k : Idx d (sz.L n) (sz.W n)) (c : ℂ) :
    condRow sz n k (fun _ => c) = fun _ => c := by
  funext ω
  simp [condRow]

/-- **`E_k ∘ E_k = E_k`.** -/
@[simp] theorem condRow_condRow (k : Idx d (sz.L n) (sz.W n)) (X : Sizes.SeqΩ sz → ℂ) :
    condRow sz n k (condRow sz n k X) = condRow sz n k X := by
  funext ω
  have h : ∀ ω' : Sizes.SeqΩ sz, condRow sz n k X (rowSplit sz n k ω ω') = condRow sz n k X ω := by
    intro ω'
    simp only [condRow, rowSplit_rowSplit]
  simp only [condRow_apply (X := condRow sz n k X), h]
  simp

/-- `E_k X` does not read row `k`: it is unchanged by the splitting. -/
theorem rowSplit_condRow (k : Idx d (sz.L n) (sz.W n)) (X : Sizes.SeqΩ sz → ℂ)
    (ω ω' : Sizes.SeqΩ sz) :
    condRow sz n k X (rowSplit sz n k ω ω') = condRow sz n k X ω := by
  simp only [condRow, rowSplit_rowSplit]

theorem condRow_sub (k : Idx d (sz.L n) (sz.W n)) {X Y : Sizes.SeqΩ sz → ℂ}
    (hX : RowIntegrable sz n k X)
    (hY : RowIntegrable sz n k Y) :
    condRow sz n k (fun ω => X ω - Y ω) = fun ω => condRow sz n k X ω - condRow sz n k Y ω := by
  funext ω
  exact integral_sub (hX ω) (hY ω)

/-- **`E_k ∘ (1 - E_k) = 0`.** -/
theorem condRow_sub_condRow (k : Idx d (sz.L n) (sz.W n)) {X : Sizes.SeqΩ sz → ℂ}
    (hX : RowIntegrable sz n k X) :
    condRow sz n k (fun ω => X ω - condRow sz n k X ω) = 0 := by
  have hcond : RowIntegrable sz n k (condRow sz n k X) := by
    intro ω
    have : (fun ω' => condRow sz n k X (rowSplit sz n k ω ω')) = fun _ => condRow sz n k X ω := by
      funext ω'; exact rowSplit_condRow k X ω ω'
    rw [this]
    exact integrable_const _
  funext ω
  rw [condRow_sub k hX hcond]
  have := congrFun (condRow_condRow k X) ω
  simp only [Pi.zero_apply, this, sub_self]

/-! #### Pulling out a factor that does not read row `k` -/

/-- **`g` is strictly independent of row `k`**: it reads only finitely many Gaussian
coordinates, and none of those is a row-`k` coordinate. -/
def FinDepOffRow {d : ℕ} (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) {V : Type*}
    (g : Sizes.SeqΩ sz → V) : Prop :=
  ∃ I : Finset (Sizes.SeqCoord sz), (∀ c ∈ I, ¬ IsRowCoord sz n k c) ∧
    ∀ ω ω' : Sizes.SeqΩ sz, (∀ c ∈ I, ω c = ω' c) → g ω = g ω'

theorem FinDepOffRow.rowSplit_eq {k : Idx d (sz.L n) (sz.W n)} {V : Type*}
    {g : Sizes.SeqΩ sz → V}
    (h : FinDepOffRow sz n k g) (ω ω' : Sizes.SeqΩ sz) : g (rowSplit sz n k ω ω') = g ω := by
  obtain ⟨I, hI, hg⟩ := h
  exact (hg ω _ fun c hc => (rowSplit_apply_of_not_isRowCoord k ω ω' (hI c hc)).symm).symm

theorem FinDepOffRow.comp {k : Idx d (sz.L n) (sz.W n)} {V W : Type*}
    {g : Sizes.SeqΩ sz → V}
    (h : FinDepOffRow sz n k g) (F : V → W) : FinDepOffRow sz n k fun ω => F (g ω) :=
  let ⟨I, hI, hg⟩ := h
  ⟨I, hI, fun ω ω' hω => show F (g ω) = F (g ω') by rw [hg ω ω' hω]⟩

/-- A function strictly independent of row `k` is its own `E_k`. -/
theorem condRow_of_finDepOffRow {k : Idx d (sz.L n) (sz.W n)} {X : Sizes.SeqΩ sz → ℂ}
    (h : FinDepOffRow sz n k X) :
    condRow sz n k X = X := by
  funext ω
  have : (fun ω' => X (rowSplit sz n k ω ω')) = fun _ => X ω := by
    funext ω'; exact h.rowSplit_eq ω ω'
  simp [condRow, this]

/-- The independent factor comes out of `E_k` on the right. -/
theorem condRow_mul_of_finDepOffRow' {k : Idx d (sz.L n) (sz.W n)}
    {X Y : Sizes.SeqΩ sz → ℂ}
    (hY : FinDepOffRow sz n k Y) :
    condRow sz n k (fun ω => X ω * Y ω) = fun ω => condRow sz n k X ω * Y ω := by
  funext ω
  have hY' : ∀ ω', Y (rowSplit sz n k ω ω') = Y ω := hY.rowSplit_eq ω
  simp only [condRow_apply, hY']
  exact integral_mul_const (Y ω) _

/-! #### The tower property `E[E_k X] = E[X]` -/

/-- **`E[E_k X] = E[X]`.** -/
theorem integral_condRow (k : Idx d (sz.L n) (sz.W n)) {X : Sizes.SeqΩ sz → ℂ}
    (hX : Integrable X (Sizes.seqP sz)) :
    ∫ ω, condRow sz n k X ω ∂(Sizes.seqP sz) = ∫ ω, X ω ∂(Sizes.seqP sz) := by
  have hmp := measurePreserving_rowSplit sz n k
  have hmap : ((Sizes.seqP sz).prod (Sizes.seqP sz)).map
      (fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2) = Sizes.seqP sz :=
    hmp.map_eq
  have hXmeas : AEStronglyMeasurable X
      (((Sizes.seqP sz).prod (Sizes.seqP sz)).map
        fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2) := by
    rw [hmap]; exact hX.aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun ω ω' => X (rowSplit sz n k ω ω'))
      ((Sizes.seqP sz).prod (Sizes.seqP sz)) := by
    refine (integrable_map_measure hXmeas (measurable_rowSplit sz n k).aemeasurable).1 ?_
    rw [hmap]; exact hX
  have hpush := integral_map (μ := (Sizes.seqP sz).prod (Sizes.seqP sz))
    (φ := fun p : Sizes.SeqΩ sz × Sizes.SeqΩ sz => rowSplit sz n k p.1 p.2) (f := X)
    (measurable_rowSplit sz n k).aemeasurable hXmeas
  rw [hmap] at hpush
  simp only [condRow_apply]
  rw [integral_integral hint]
  exact hpush.symm

/-! ### Strict independence of the minor resolvent `G^{(k)}` -/

/-- **The master row-independence lemma.**  Anything read off the minor matrix
`H_u^{(k)} = (H_u).submatrix (· ≠ k) (· ≠ k)` is strictly independent of row `k`. -/
theorem finDepOffRow_of_minor (sz : Sizes d) (n : ℕ) (u : ℝ) (k : Idx d (sz.L n) (sz.W n))
    {V : Type*}
    (F : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ k}
      {a : Idx d (sz.L n) (sz.W n) // a ≠ k} ℂ → V) :
    FinDepOffRow sz n k fun ω =>
      F ((Sizes.seqHflow sz n u ω).submatrix
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ k} → Idx d (sz.L n) (sz.W n))
        (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ k} → Idx d (sz.L n) (sz.W n))) := by
  refine ⟨offRowCoord sz n k, fun c hc => (Finset.mem_sdiff.1 hc).2, fun ω ω' hω => ?_⟩
  change F _ = F _
  rw [Hflow_submatrix_congr_offRowCoord u hω]

/-- The **minor resolvent** `G^{(k)} = (H_u^{(k)} - z)⁻¹`, as a *total* function of `ω`. -/
noncomputable def greenMinorMat {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ k} {a : Idx d (sz.L n) (sz.W n) // a ≠ k} ℂ :=
  ((Sizes.seqHflow sz n u ω).submatrix
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ k} → Idx d (sz.L n) (sz.W n))
    (Subtype.val : {a : Idx d (sz.L n) (sz.W n) // a ≠ k} → Idx d (sz.L n) (sz.W n))
      - z • (1 : Matrix {a : Idx d (sz.L n) (sz.W n) // a ≠ k}
        {a : Idx d (sz.L n) (sz.W n) // a ≠ k} ℂ))⁻¹

/-- **`G^{(k)}` is strictly independent of row `k`.** -/
theorem finDepOffRow_greenMinorMat (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) :
    FinDepOffRow sz n k (greenMinorMat sz n u z k) :=
  finDepOffRow_of_minor sz n u k fun M => (M - z • 1)⁻¹

/-- Entrywise form of `finDepOffRow_greenMinorMat`. -/
theorem finDepOffRow_greenMinorMat_apply (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (k : Idx d (sz.L n) (sz.W n))
    (a b : {a : Idx d (sz.L n) (sz.W n) // a ≠ k}) :
    FinDepOffRow sz n k fun ω => greenMinorMat sz n u z k ω a b :=
  (finDepOffRow_greenMinorMat sz n u z k).comp fun M => M a b

/-- `greenMinorMat` is the paper's `G^{(k)}`: where the full resolvent exists and `G_{kk} ≠ 0`,
it is the explicit minor formula (4.9). -/
theorem greenMinorMat_eq_minorGreen (sz : Sizes d) (n : ℕ) (u : ℝ) (z : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz)
    (hdet : IsUnit (Sizes.seqHflow sz n u ω
      - z • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)).det)
    (hGkk : green (Sizes.seqHflow sz n u ω) z k k ≠ 0) :
    greenMinorMat sz n u z k ω = minorGreen (green (Sizes.seqHflow sz n u ω) z) k :=
  inv_minor_resolvent hdet k hGkk

end CondRow

/-! ## The resolvent as a differentiable function of the Gaussian coordinates (GreenDeriv) -/

/-! ### Coordinate enumeration -/

/-- The coordinate of the common sample space attached to a coordinate `c` at size `n`. -/
abbrev crd {d : ℕ} (sz : Sizes d) (n : ℕ) (c : CoordF d (sz.L n) (sz.W n)) :
    Sizes.SeqCoord sz := ⟨n, c⟩

theorem GreenDeriv_crd_injective {d : ℕ} (sz : Sizes d) (n : ℕ) :
    Function.Injective (crd sz n) := by
  rintro p q h
  simpa using h

/-- The size slice of the common sample space reads the coordinates `crd sz n c`. -/
theorem GreenDeriv_slice_apply {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : Sizes.SeqΩ sz)
    (c : CoordF d (sz.L n) (sz.W n)) : Sizes.slice sz n ω c = ω (crd sz n c) := rfl

/-! ### The coordinate directions -/

section Directions

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The Hermitian matrix direction attached to the coordinate `(i, j, b)`:
`E_ij + E_ji` for the real tag `b = true` and `I·E_ij - I·E_ji` for the imaginary tag
`b = false`; on the diagonal `i = j` the real tag gives `E_ii`. -/
noncomputable def Bmat (i j : Idx d L W) (b : Bool) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun k l =>
    if k = i ∧ l = j then (if b then 1 else Complex.I)
    else if k = j ∧ l = i then (if b then 1 else -Complex.I)
    else 0

omit [NeZero L] [NeZero W] in
theorem GreenDeriv_Bmat_apply (i j : Idx d L W) (b : Bool) (k l : Idx d L W) :
    Bmat d L W i j b k l =
      if k = i ∧ l = j then (if b then 1 else Complex.I)
      else if k = j ∧ l = i then (if b then 1 else -Complex.I)
      else 0 := rfl

variable {d L W} in
theorem GreenDeriv_mem_usedCoords {c : CoordF d L W} :
    c ∈ usedCoords d L W ↔
      idxKey d L W c.1 < idxKey d L W c.2.1 ∨ (c.1 = c.2.1 ∧ c.2.2 = true) := by
  simp [usedCoords]

/-- **The coordinate decomposition of `X`.**  `X` is the `ℝ`-linear combination of the fixed
Hermitian directions `Bmat` with the used Gaussian coordinates as coefficients. -/
theorem Xmat_eq_sum (ω : Ω d L W) :
    Xmat d L W ω = ∑ c ∈ usedCoords d L W, ω c • Bmat d L W c.1 c.2.1 c.2.2 := by
  ext k l
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Complex.real_smul]
  rcases idxKey_lt_or_eq_or_lt d L W k l with h | h | h
  · -- `idxKey k < idxKey l`
    have hkl : k ≠ l := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(k, l, true), (k, l, false)} : Finset (CoordF d L W)) ⊆ usedCoords d L W := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact GreenDeriv_mem_usedCoords.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · change Xentry d L W ω k l = _
      rw [Xentry, ite_eq_left h]
      simp [GreenDeriv_Bmat_apply]
      ring
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := GreenDeriv_mem_usedCoords.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
      have hne1 : ¬ (k = i ∧ l = j) := by
        rintro ⟨rfl, rfl⟩
        cases b <;> simp at hnx
      have hne2 : ¬ (k = j ∧ l = i) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (asymm h)
        · exact hkl hu.1.symm
      simp [GreenDeriv_Bmat_apply, hne1, hne2]
  · -- `k = l`
    subst h
    have hsub : ({(k, k, true)} : Finset (CoordF d L W)) ⊆ usedCoords d L W := by
      intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      exact GreenDeriv_mem_usedCoords.2 (Or.inr ⟨rfl, rfl⟩)
    rw [← Finset.sum_subset hsub, Finset.sum_singleton]
    · change Xentry d L W ω k k = _
      rw [Xentry, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
      simp [GreenDeriv_Bmat_apply]
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := GreenDeriv_mem_usedCoords.1 hx
      simp only [Finset.mem_singleton] at hnx
      have hne : ¬ (k = i ∧ k = j) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (lt_irrefl _)
        · have hb : b = true := hu.2
          subst hb
          exact hnx rfl
      have hne' : ¬ (k = j ∧ k = i) := fun h' => hne ⟨h'.2, h'.1⟩
      rw [GreenDeriv_Bmat_apply, ite_eq_right hne, ite_eq_right hne', mul_zero]
  · -- `idxKey l < idxKey k`
    have hkl : l ≠ k := fun he => absurd (he ▸ h) (lt_irrefl _)
    have hsub : ({(l, k, true), (l, k, false)} : Finset (CoordF d L W)) ⊆ usedCoords d L W := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact GreenDeriv_mem_usedCoords.2 (Or.inl h)
    rw [← Finset.sum_subset hsub, Finset.sum_pair (by simp)]
    · change Xentry d L W ω k l = _
      rw [Xentry, ite_eq_right (asymm h), ite_eq_left h]
      simp [GreenDeriv_Bmat_apply, hkl, Ne.symm hkl]
      ring
    · rintro ⟨i, j, b⟩ hx hnx
      have hu := GreenDeriv_mem_usedCoords.1 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hnx
      have hne1 : ¬ (k = i ∧ l = j) := by
        rintro ⟨rfl, rfl⟩
        rcases hu with hu | hu
        · exact absurd hu (asymm h)
        · exact hkl hu.1.symm
      have hne2 : ¬ (k = j ∧ l = i) := by
        rintro ⟨rfl, rfl⟩
        cases b <;> simp at hnx
      simp [GreenDeriv_Bmat_apply, hne1, hne2]

variable {d L W} in
/-- Every direction attached to a **used** coordinate is Hermitian (the redundant coordinate
`(i, i, false)` is the one exception, and it is never read). -/
theorem GreenDeriv_Bmat_isHermitian {c : CoordF d L W} (hc : c ∈ usedCoords d L W) :
    (Bmat d L W c.1 c.2.1 c.2.2).IsHermitian := by
  obtain ⟨i, j, b⟩ := c
  have hij : i ≠ j ∨ b = true := by
    rcases GreenDeriv_mem_usedCoords.1 hc with h | h
    · exact Or.inl fun he => absurd (he ▸ h) (lt_irrefl _)
    · exact Or.inr h.2
  ext k l
  change (starRingEnd ℂ) (Bmat d L W i j b l k) = Bmat d L W i j b k l
  rw [GreenDeriv_Bmat_apply, GreenDeriv_Bmat_apply]
  rcases hij with hij | hb
  · by_cases hA : k = i ∧ l = j
    · have hB : ¬ (l = i ∧ k = j) := fun hB => hij (by rw [← hA.1]; exact hB.2)
      rw [ite_eq_right hB, ite_eq_left (⟨hA.2, hA.1⟩ : l = j ∧ k = i), ite_eq_left hA]
      cases b <;> simp
    · by_cases hB : k = j ∧ l = i
      · rw [ite_eq_left (⟨hB.2, hB.1⟩ : l = i ∧ k = j), ite_eq_right hA, ite_eq_left hB]
        cases b <;> simp
      · rw [ite_eq_right (fun h => hB ⟨h.2, h.1⟩), ite_eq_right (fun h => hA ⟨h.2, h.1⟩),
          ite_eq_right hA, ite_eq_right hB]
        simp
  · subst hb
    by_cases hA : k = i ∧ l = j
    · rw [ite_eq_left hA]
      by_cases hB : l = i ∧ k = j
      · rw [ite_eq_left hB]; simp
      · rw [ite_eq_right hB, ite_eq_left (⟨hA.2, hA.1⟩ : l = j ∧ k = i)]; simp
    · rw [ite_eq_right hA]
      by_cases hB : k = j ∧ l = i
      · rw [ite_eq_left (⟨hB.2, hB.1⟩ : l = i ∧ k = j), ite_eq_left hB]; simp
      · rw [ite_eq_right (fun h => hB ⟨h.2, h.1⟩), ite_eq_right (fun h => hA ⟨h.2, h.1⟩),
          ite_eq_right hB]
        simp

variable {d L W} in
/-- On a used coordinate the merged direction `coordinateMatrix` is `Bmat`.  (Off the used
coordinates `coordinateMatrix` is `0`, `coordinateMatrix_zero_of_not_mem_usedCoords`.) -/
theorem GreenDeriv_coordinateMatrix_eq_Bmat {c : CoordF d L W} (hc : c ∈ usedCoords d L W) :
    coordinateMatrix d L W c = Bmat d L W c.1 c.2.1 c.2.2 := by
  classical
  rw [coordinateMatrix, Xmat_eq_sum, Finset.sum_eq_single_of_mem c hc]
  · simp
  · intro c' _ hne
    rw [Pi.single_eq_of_ne hne, zero_smul]

variable {d L W} in
/-- **`X` is affine in each used coordinate**, with slope the direction `Bmat`. -/
theorem GreenDeriv_Xmat_update (ω : Ω d L W) {c : CoordF d L W} (hc : c ∈ usedCoords d L W)
    (t : ℝ) :
    Xmat d L W (Function.update ω c t)
      = Xmat d L W ω + (t - ω c) • Bmat d L W c.1 c.2.1 c.2.2 := by
  rw [Xmat_update, GreenDeriv_coordinateMatrix_eq_Bmat hc]

end Directions

/-! ### The sequence model -/

section Sequence

variable {d : ℕ} (sz : Sizes d)

/-- The coordinate decomposition of the size-`n` matrix on the common sample space. -/
theorem GreenDeriv_seqXmat_eq_sum (n : ℕ) (ω : Sizes.SeqΩ sz) :
    Sizes.seqXmat sz n ω =
      ∑ c ∈ usedCoords d (sz.L n) (sz.W n),
        ω (crd sz n c) • Bmat d (sz.L n) (sz.W n) c.1 c.2.1 c.2.2 :=
  Xmat_eq_sum _ _ _ _

/-- Moving the common-space coordinate `crd sz n c` of a used `c` moves `seqXmat sz n` along
`Bmat c`. -/
theorem GreenDeriv_seqXmat_update (n : ℕ) (ω : Sizes.SeqΩ sz) {c : CoordF d (sz.L n) (sz.W n)}
    (hc : c ∈ usedCoords d (sz.L n) (sz.W n)) (t : ℝ) :
    Sizes.seqXmat sz n (Function.update ω (crd sz n c) t) =
      Sizes.seqXmat sz n ω
        + (t - ω (crd sz n c)) • Bmat d (sz.L n) (sz.W n) c.1 c.2.1 c.2.2 := by
  rw [Sizes.seqXmat_update, GreenDeriv_coordinateMatrix_eq_Bmat hc]

/-- The flow on the common space, with the real scalar action. -/
theorem GreenDeriv_seqHflow_eq_realSmul (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ sz) :
    Sizes.seqHflow sz n u ω = Real.sqrt u • Sizes.seqXmat sz n ω :=
  Hflow_eq_realSmul _ _ _ _ _

/-- The flow at size `n` is continuous in the common-space coordinates. -/
theorem GreenDeriv_continuous_seqHflow (n : ℕ) (u : ℝ) :
    Continuous (Sizes.seqHflow sz n u) := by
  have hs : Continuous (Sizes.slice sz n) :=
    continuous_pi fun c => continuous_apply (crd sz n c)
  exact (continuous_Hflow d (sz.L n) (sz.W n) u).comp hs

/-- `seqHflow sz n u` reads only the coordinates `crd sz n c`, `c ∈ usedCoords`. -/
theorem GreenDeriv_seqHflow_congr_of_agree (n : ℕ) (u : ℝ) (ω ω' : Sizes.SeqΩ sz)
    (h : ∀ e ∈ (usedCoords d (sz.L n) (sz.W n)).image (crd sz n), ω e = ω' e) :
    Sizes.seqHflow sz n u ω = Sizes.seqHflow sz n u ω' := by
  rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqHflow_eq_realSmul,
    GreenDeriv_seqXmat_eq_sum, GreenDeriv_seqXmat_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [h (crd sz n c) (Finset.mem_image_of_mem _ hc)]

/-- Anything read off `seqHflow sz n u` reads only finitely many coordinates. -/
theorem finDep_of_Hflow (n : ℕ) (u : ℝ) {V : Type*}
    (F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → V) :
    FinDep sz fun ω => F (Sizes.seqHflow sz n u ω) :=
  ⟨(usedCoords d (sz.L n) (sz.W n)).image (crd sz n), fun ω ω' h => by
    change F (Sizes.seqHflow sz n u ω) = F (Sizes.seqHflow sz n u ω')
    rw [GreenDeriv_seqHflow_congr_of_agree sz n u ω ω' h]⟩

end Sequence

/-! ### The Hermitian projection and the extended resolvent -/

section HermProj

open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `ℝ`-linear projection onto the Hermitian matrices, `M ↦ (M + Mᴴ)/2`, as a continuous
linear map (hence `C^∞`). -/
noncomputable def hermCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
      map_add' := by
        intro M M'
        rw [Matrix.conjTranspose_add]
        module
      map_smul' := by
        intro r M
        rw [RingHom.id_apply, Matrix.conjTranspose_smul, star_trivial]
        module }

theorem GreenDeriv_hermCLM_apply (M : Matrix n n ℂ) :
    hermCLM n M = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M) := rfl

/-- The projection lands in the Hermitian matrices. -/
theorem GreenDeriv_isHermitian_hermCLM (M : Matrix n n ℂ) : (hermCLM n M).IsHermitian := by
  change Matrix.conjTranspose ((2⁻¹ : ℝ) • (M + Matrix.conjTranspose M))
      = (2⁻¹ : ℝ) • (M + Matrix.conjTranspose M)
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose, add_comm]

/-- The projection is the identity on Hermitian matrices. -/
theorem GreenDeriv_hermCLM_of_isHermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    hermCLM n M = M := by
  rw [GreenDeriv_hermCLM_apply, hM]
  module

/-- **`G_z` pre-composed with the Hermitian projection**: defined on the whole matrix space,
and equal to the Green function at every Hermitian matrix
(`GreenDeriv_resH_of_isHermitian`). -/
noncomputable def resH (z : ℂ) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  Ring.inverse (hermCLM n M - z • (1 : Matrix n n ℂ))

theorem GreenDeriv_resH_eq_green (z : ℂ) (M : Matrix n n ℂ) :
    resH z M = green (hermCLM n M) z := by
  change Ring.inverse (hermCLM n M - z • (1 : Matrix n n ℂ))
    = (hermCLM n M - z • (1 : Matrix n n ℂ))⁻¹
  rw [Matrix.nonsing_inv_eq_ringInverse]

theorem GreenDeriv_resH_of_isHermitian {z : ℂ} {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    resH z M = green M z := by
  rw [GreenDeriv_resH_eq_green, GreenDeriv_hermCLM_of_isHermitian hM]

theorem GreenDeriv_isUnit_resH_arg {z : ℂ} (hz : z.im ≠ 0) (M : Matrix n n ℂ) :
    IsUnit (hermCLM n M - z • (1 : Matrix n n ℂ)) :=
  RBM.isUnit_sub_smul_of_isHermitian (GreenDeriv_isHermitian_hermCLM M) hz

/-- **The real Fréchet derivative of the extended resolvent**:
`D resH_z(M)[A] = -resH_z(M) · herm(A) · resH_z(M)`, for every `M` and `Im z ≠ 0`. -/
theorem hasFDerivAt_resH {z : ℂ} (hz : z.im ≠ 0) (M : Matrix n n ℂ) :
    HasFDerivAt (resH z)
      (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) (resH z M) (resH z M)).comp
        (hermCLM n))) M := by
  obtain ⟨u, hus⟩ : ∃ u : (Matrix n n ℂ)ˣ,
      (u : Matrix n n ℂ) = hermCLM n M - z • (1 : Matrix n n ℂ) :=
    ⟨(GreenDeriv_isUnit_resH_arg hz M).unit, IsUnit.unit_spec _⟩
  have hinv : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = resH z M := by
    rw [resH, ← hus, Ring.inverse_unit]
  have hT : HasFDerivAt (fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ))
      (hermCLM n) M := (hermCLM n).hasFDerivAt.sub_const _
  have hF : HasFDerivAt (Ring.inverse (M₀ := Matrix n n ℂ))
      (-((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) ↑u⁻¹) ↑u⁻¹))
      ((fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ)) M) := by
    change HasFDerivAt _ _ (hermCLM n M - z • (1 : Matrix n n ℂ))
    rw [← hus]
    exact hasFDerivAt_ringInverse u
  have key := hF.comp M hT
  rw [hinv] at key
  have hcomp : (Ring.inverse (M₀ := Matrix n n ℂ))
      ∘ (fun M' : Matrix n n ℂ => hermCLM n M' - z • (1 : Matrix n n ℂ)) = resH z := rfl
  rw [hcomp, ContinuousLinearMap.neg_comp] at key
  exact key

/-- **Continuity of `t ↦ G_t`.**  The resolvent depends continuously on a continuously varying
Hermitian matrix. -/
theorem continuous_green_comp {V : Type*} [TopologicalSpace V]
    {f : V → Matrix n n ℂ} (hf : Continuous f)
    (hherm : ∀ v, (f v).IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun v => green (f v) z :=
  (RBM.Gauss.continuous_green_of_isHermitian hf hherm hz).congr fun v => by
    simp only [Gres, green, ite_true, Matrix.nonsing_inv_eq_ringInverse]

end HermProj

/-! ## Fluctuation averaging, base layer: the vanishing lemma and the weights (FlucVanish) -/

/-! ### `(A - m • 1)_{ij}` -/

section Det

variable {n : Type*} [DecidableEq n]

/-- Entries of `G - m` are `G_{ij} - m δ_{ij}`. -/
theorem sub_smul_one_apply (A : Matrix n n ℂ) (m : ℂ) (i j : n) :
    (A - m • (1 : Matrix n n ℂ)) i j = A i j - (if i = j then m else 0) := by
  by_cases h : i = j
  · subst h
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne h, h]

end Det

section Vanish0

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-! ### Closure properties of `FinDepOffRow` -/

theorem finDepOffRow_const (k : Idx d (sz.L n) (sz.W n)) {V : Type*} (v : V) :
    FinDepOffRow sz n k (fun _ : Sizes.SeqΩ sz => v) :=
  ⟨∅, by simp, fun _ _ _ => rfl⟩

theorem FinDepOffRow.mul {k : Idx d (sz.L n) (sz.W n)} {X Y : Sizes.SeqΩ sz → ℂ}
    (hX : FinDepOffRow sz n k X)
    (hY : FinDepOffRow sz n k Y) : FinDepOffRow sz n k fun ω => X ω * Y ω := by
  classical
  obtain ⟨I, hI, hX'⟩ := hX
  obtain ⟨J, hJ, hY'⟩ := hY
  refine ⟨I ∪ J, ?_, fun ω ω' hω => ?_⟩
  · intro c hc
    rcases Finset.mem_union.1 hc with h | h
    · exact hI c h
    · exact hJ c h
  · change X ω * Y ω = X ω' * Y ω'
    rw [hX' ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
      hY' ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

theorem FinDepOffRow.sub {k : Idx d (sz.L n) (sz.W n)} {X Y : Sizes.SeqΩ sz → ℂ}
    (hX : FinDepOffRow sz n k X)
    (hY : FinDepOffRow sz n k Y) : FinDepOffRow sz n k fun ω => X ω - Y ω := by
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

/-- **A finite product of factors independent of row `k` is independent of row `k`.** -/
theorem finDepOffRow_prod {k : Idx d (sz.L n) (sz.W n)} {ι : Type*} (s : Finset ι)
    {f : ι → Sizes.SeqΩ sz → ℂ}
    (hf : ∀ i ∈ s, FinDepOffRow sz n k (f i)) :
    FinDepOffRow sz n k fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simpa using finDepOffRow_const k (1 : ℂ)
  | cons j t hj ih =>
      have hjf : FinDepOffRow sz n k (f j) := hf j (Finset.mem_cons_self _ _)
      have ht : FinDepOffRow sz n k fun ω => ∏ i ∈ t, f i ω :=
        ih fun i hi => hf i (Finset.mem_cons_of_mem hi)
      have := hjf.mul ht
      simpa only [Finset.prod_cons] using this

/-- **`E_{k'}` preserves independence of row `k`.** -/
theorem finDepOffRow_condRow {k k' : Idx d (sz.L n) (sz.W n)} {X : Sizes.SeqΩ sz → ℂ}
    (h : FinDepOffRow sz n k X) :
    FinDepOffRow sz n k (condRow sz n k' X) := by
  classical
  obtain ⟨I, hI, hX⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord sz n k' c, fun c hc => hI c (Finset.mem_filter.1 hc).1,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hX _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord sz n k' c
  · rw [rowSplit_apply_of_isRowCoord k' ω ω'' hcr, rowSplit_apply_of_isRowCoord k' ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k' ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k' ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

/-! ### Integrability from measurability and a uniform bound -/

/-- A bounded measurable function on the Gaussian product space is integrable. -/
theorem integrable_P_of_measurable_of_bound {f : Sizes.SeqΩ sz → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f (Sizes.seqP sz) :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-! ### The vanishing lemma, abstract form -/

section Vanish

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The vanishing itself.**  If every factor other than the distinguished one is strictly
independent of row `κ`, and the distinguished factor is killed by `E_κ`, then the expectation
of the product is exactly `0`. -/
theorem integral_mul_prod_eq_zero {κ : Idx d (sz.L n) (sz.W n)} {i₀ : ι}
    {Z Y : ι → Sizes.SeqΩ sz → ℂ}
    (hZ0 : condRow sz n κ (Z i₀) = 0)
    (hY : ∀ i ∈ Finset.univ.erase i₀, FinDepOffRow sz n κ (Y i))
    (hint : Integrable (fun ω => Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Y i ω) (Sizes.seqP sz)) :
    ∫ ω, Z i₀ ω * ∏ i ∈ Finset.univ.erase i₀, Y i ω ∂(Sizes.seqP sz) = 0 := by
  have hprod : FinDepOffRow sz n κ fun ω => ∏ i ∈ Finset.univ.erase i₀, Y i ω :=
    finDepOffRow_prod _ hY
  have hpull := condRow_mul_of_finDepOffRow' (X := Z i₀)
    (Y := fun ω => ∏ i ∈ Finset.univ.erase i₀, Y i ω) hprod
  rw [← integral_condRow κ hint, hpull]
  simp [hZ0]

end Vanish

end Vanish0

/-! ### The concrete fluctuation `Z_k = (1 - E_k)(G_{kk} - m)` -/

/-- The centred diagonal Green function entry, `G_{kk} - m`. -/
noncomputable def greenDiagCentered {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) : Sizes.SeqΩ sz → ℂ :=
  fun ω => green (Sizes.seqHflow sz n u ω) z k k - m

/-- **`Z_k := (1 - E_k)(G_{kk} - m)`**, the fluctuation. -/
noncomputable def flucDiag {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) : Sizes.SeqΩ sz → ℂ :=
  fun ω => greenDiagCentered sz n u z m k ω - condRow sz n k (greenDiagCentered sz n u z m k) ω

/-- The centred diagonal entry of the **minor** resolvent, `G^{(κ)}_{kk} - m`. -/
noncomputable def greenMinorDiagCentered {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Sizes.SeqΩ sz → ℂ :=
  fun ω => greenMinorMat sz n u z κ ω k k - m

/-- **`Z^{(κ)}_k := (1 - E_k)(G^{(κ)}_{kk} - m)`**, the replaced fluctuation. -/
noncomputable def flucDiagMinor {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (κ : Idx d (sz.L n) (sz.W n)) (k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}) :
    Sizes.SeqΩ sz → ℂ :=
  fun ω => greenMinorDiagCentered sz n u z m κ k ω
    - condRow sz n k.1 (greenMinorDiagCentered sz n u z m κ k) ω

section Fluc

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-- **The replacement error of a factor**, in terms of the replacement error of the Green
function entry; the factor `2` is the price of the `(1 - E_k)`. -/
theorem norm_flucDiag_sub_flucDiagMinor_le {u : ℝ} {z m : ℂ} {κ : Idx d (sz.L n) (sz.W n)}
    {k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}} {e : ℝ}
    (hrow : RowIntegrable sz n k.1 (greenDiagCentered sz n u z m k.1))
    (hrow' : RowIntegrable sz n k.1 (greenMinorDiagCentered sz n u z m κ k))
    (he : ∀ ω, ‖green (Sizes.seqHflow sz n u ω) z k.1 k.1 - greenMinorMat sz n u z κ ω k k‖ ≤ e)
    (ω : Sizes.SeqΩ sz) :
    ‖flucDiag sz n u z m k.1 ω - flucDiagMinor sz n u z m κ k ω‖ ≤ 2 * e := by
  have hD : ∀ ω' : Sizes.SeqΩ sz, greenDiagCentered sz n u z m k.1 ω'
      - greenMinorDiagCentered sz n u z m κ k ω'
      = green (Sizes.seqHflow sz n u ω') z k.1 k.1 - greenMinorMat sz n u z κ ω' k k := by
    intro ω'
    simp only [greenDiagCentered, greenMinorDiagCentered]
    ring
  have hcond := condRow_sub k.1 hrow hrow'
  have hcondpt : condRow sz n k.1 (greenDiagCentered sz n u z m k.1) ω
      - condRow sz n k.1 (greenMinorDiagCentered sz n u z m κ k) ω
      = condRow sz n k.1 (fun ω' => green (Sizes.seqHflow sz n u ω') z k.1 k.1
          - greenMinorMat sz n u z κ ω' k k) ω := by
    have := congrFun hcond ω
    rw [← this]
    simp only [condRow_apply, hD]
  have hbound : ‖condRow sz n k.1 (fun ω' => green (Sizes.seqHflow sz n u ω') z k.1 k.1
      - greenMinorMat sz n u z κ ω' k k) ω‖ ≤ e := by
    rw [condRow_apply]
    have := norm_integral_le_of_norm_le_const (μ := Sizes.seqP sz)
      (f := fun ω' => green (Sizes.seqHflow sz n u (rowSplit sz n k.1 ω ω')) z k.1 k.1
        - greenMinorMat sz n u z κ (rowSplit sz n k.1 ω ω') k k)
      (C := e) (Filter.Eventually.of_forall fun ω' => he _)
    simpa using this
  have hsplit : flucDiag sz n u z m k.1 ω - flucDiagMinor sz n u z m κ k ω
      = (green (Sizes.seqHflow sz n u ω) z k.1 k.1 - greenMinorMat sz n u z κ ω k k)
        - condRow sz n k.1 (fun ω' => green (Sizes.seqHflow sz n u ω') z k.1 k.1
            - greenMinorMat sz n u z κ ω' k k) ω := by
    rw [← hcondpt, ← hD ω]
    simp only [flucDiag, flucDiagMinor]
    ring
  rw [hsplit]
  calc ‖(green (Sizes.seqHflow sz n u ω) z k.1 k.1 - greenMinorMat sz n u z κ ω k k)
        - condRow sz n k.1 (fun ω' => green (Sizes.seqHflow sz n u ω') z k.1 k.1
            - greenMinorMat sz n u z κ ω' k k) ω‖
      ≤ ‖green (Sizes.seqHflow sz n u ω) z k.1 k.1 - greenMinorMat sz n u z κ ω k k‖
        + ‖condRow sz n k.1 (fun ω' => green (Sizes.seqHflow sz n u ω') z k.1 k.1
            - greenMinorMat sz n u z κ ω' k k) ω‖ := norm_sub_le _ _
    _ ≤ e + e := add_le_add (he ω) hbound
    _ = 2 * e := by ring

/-- **A uniform bound survives `(1 - E_k)`, at the cost of a factor `2`.** -/
theorem norm_sub_condRow_le {k : Idx d (sz.L n) (sz.W n)} {X : Sizes.SeqΩ sz → ℂ} {b : ℝ}
    (hX : ∀ ω, ‖X ω‖ ≤ b)
    (ω : Sizes.SeqΩ sz) : ‖X ω - condRow sz n k X ω‖ ≤ 2 * b := by
  have h1 : ‖condRow sz n k X ω‖ ≤ b := by
    rw [condRow_apply]
    simpa using norm_integral_le_of_norm_le_const (μ := Sizes.seqP sz)
      (f := fun ω' => X (rowSplit sz n k ω ω')) (C := b)
      (Filter.Eventually.of_forall fun ω' => hX _)
  calc ‖X ω - condRow sz n k X ω‖ ≤ ‖X ω‖ + ‖condRow sz n k X ω‖ := norm_sub_le _ _
    _ ≤ b + b := add_le_add (hX ω) h1
    _ = 2 * b := by ring

/-- `‖Z_k‖ ≤ 2 b` as soon as `‖G_{kk} - m‖ ≤ b` uniformly. -/
theorem norm_flucDiag_le {u : ℝ} {z m : ℂ} {k : Idx d (sz.L n) (sz.W n)} {b : ℝ}
    (hb : ∀ ω, ‖greenDiagCentered sz n u z m k ω‖ ≤ b) (ω : Sizes.SeqΩ sz) :
    ‖flucDiag sz n u z m k ω‖ ≤ 2 * b :=
  norm_sub_condRow_le hb ω

/-- `‖Z^{(κ)}_k‖ ≤ 2 b` as soon as `‖G^{(κ)}_{kk} - m‖ ≤ b` uniformly. -/
theorem norm_flucDiagMinor_le {u : ℝ} {z m : ℂ} {κ : Idx d (sz.L n) (sz.W n)}
    {k : {a : Idx d (sz.L n) (sz.W n) // a ≠ κ}}
    {b : ℝ} (hb : ∀ ω, ‖greenMinorDiagCentered sz n u z m κ k ω‖ ≤ b) (ω : Sizes.SeqΩ sz) :
    ‖flucDiagMinor sz n u z m κ k ω‖ ≤ 2 * b :=
  norm_sub_condRow_le hb ω

end Fluc

/-! ### Uniform and bounded weights -/

section Counting

variable {κ : Type*}

/-- **A uniform weight**: `t_k = c` on a set `A` and `0` off it, with total mass `c · #A ≤ 1`.
The block average `k ↦ W^{-d} 1(k ∈ 𝓘_a)` is of this shape at every `d`
(`uniformWeight_blockAvg2`); the row `j ↦ S_{ij}` is not one for `g² ≠ 1`
(`not_uniformWeight_svarF`): it carries the coupling `g` and takes two nonzero values on its
support.  See `BoundedWeight`, `boundedWeight_svarF`. -/
structure UniformWeight (t : κ → ℝ) (c : ℝ) (A : Finset κ) : Prop where
  /-- The common value is nonnegative. -/
  nonneg : 0 ≤ c
  /-- `t` is `c` on `A` … -/
  mem : ∀ k ∈ A, t k = c
  /-- … and `0` off it. -/
  not_mem : ∀ k ∉ A, t k = 0
  /-- Total mass at most one, the normalization `∑_k |t_k| ≤ 1`. -/
  mass : c * A.card ≤ 1

/-- **A bounded weight** (Amend 1 of T2061, DECISIONS §30; paper-delta candidate `T2061a`):
`0 ≤ t_k ≤ c` on a set `A`, `t_k = 0` off it, total mass `∑_k t_k ≤ 1`.  The weaker form of
`UniformWeight` in which `t = c` is relaxed to `t ≤ c` and the mass bound `c · #A ≤ 1` is replaced
by the bound `∑ t ≤ 1` on the actual mass.  The row `j ↦ S_{ij}` of the variance profile is a
bounded weight at every `d ≥ 3` (`boundedWeight_svarF`). -/
structure BoundedWeight [Fintype κ] (t : κ → ℝ) (c : ℝ) (A : Finset κ) : Prop where
  /-- The bound is nonnegative. -/
  nonneg_c : 0 ≤ c
  /-- Every weight is nonnegative. -/
  nonneg : ∀ k, 0 ≤ t k
  /-- `t` is at most `c` on `A` … -/
  le : ∀ k ∈ A, t k ≤ c
  /-- … and `0` off it. -/
  not_mem : ∀ k ∉ A, t k = 0
  /-- Total mass at most one, `∑_k t_k ≤ 1`. -/
  sum_le : ∑ k, t k ≤ 1

/-- A uniform weight is a bounded weight (`∑ t = c · #A ≤ 1`). -/
theorem UniformWeight.toBoundedWeight [Fintype κ] {t : κ → ℝ} {c : ℝ} {A : Finset κ}
    (h : UniformWeight t c A) : BoundedWeight t c A where
  nonneg_c := h.nonneg
  nonneg := fun k => by
    by_cases hk : k ∈ A
    · rw [h.mem k hk]; exact h.nonneg
    · rw [h.not_mem k hk]
  le := fun k hk => (h.mem k hk).le
  not_mem := h.not_mem
  sum_le := by
    rw [← Finset.sum_subset (Finset.subset_univ A) (fun k _ hk => h.not_mem k hk),
      Finset.sum_congr rfl h.mem, Finset.sum_const, nsmul_eq_mul, mul_comm]
    exact h.mass

end Counting

/-! ### The conjugation pattern -/

section Eps

/-- The ring homomorphism attached to the slot `i`: the identity on the left summand, complex
conjugation on the right. -/
def epsHom (p : ℕ) : (Fin p ⊕ Fin p) → (ℂ →+* ℂ) :=
  Sum.elim (fun _ => RingHom.id ℂ) fun _ => starRingEnd ℂ

@[simp] theorem epsHom_inl (p : ℕ) (i : Fin p) (w : ℂ) : epsHom p (Sum.inl i) w = w := rfl

@[simp] theorem epsHom_inr (p : ℕ) (i : Fin p) (w : ℂ) :
    epsHom p (Sum.inr i) w = (starRingEnd ℂ) w := rfl

@[simp] theorem norm_epsHom (p : ℕ) (i : Fin p ⊕ Fin p) (w : ℂ) : ‖epsHom p i w‖ = ‖w‖ := by
  cases i <;> simp

@[simp] theorem epsHom_ofReal (p : ℕ) (i : Fin p ⊕ Fin p) (r : ℝ) :
    epsHom p i (r : ℂ) = (r : ℂ) := by
  cases i <;> simp

theorem measurable_epsHom (p : ℕ) (i : Fin p ⊕ Fin p) : Measurable (epsHom p i) := by
  cases i with
  | inl _ => exact measurable_id
  | inr _ => exact Complex.continuous_conj.measurable

/-- **`|w|^{2p}` as a product of `2p` factors**, `p` of them conjugated. -/
theorem prod_epsHom (p : ℕ) (w : ℂ) : ∏ i, epsHom p i w = ((‖w‖ ^ (2 * p) : ℝ) : ℂ) := by
  rw [Fintype.prod_sum_type]
  simp only [epsHom_inl, epsHom_inr, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow, Complex.mul_conj', ← pow_mul]
  push_cast
  ring

/-- **The multi-index expansion** of `|∑_k t_k Z_k|^{2p}`. -/
theorem prod_epsHom_sum_eq (p : ℕ) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (Z : κ → ℂ) :
    ((‖∑ k, (t k : ℂ) * Z k‖ ^ (2 * p) : ℝ) : ℂ)
      = ∑ v : (Fin p ⊕ Fin p) → κ,
          (∏ i, (t (v i) : ℂ)) * ∏ i, epsHom p i (Z (v i)) := by
  classical
  rw [← prod_epsHom]
  have h1 : ∀ i : Fin p ⊕ Fin p, epsHom p i (∑ k, (t k : ℂ) * Z k)
      = ∑ k, (t k : ℂ) * epsHom p i (Z k) := by
    intro i
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, epsHom_ofReal]
  simp_rw [h1]
  rw [Finset.prod_univ_sum (fun _ : Fin p ⊕ Fin p => (univ : Finset κ))
      fun (i : Fin p ⊕ Fin p) (k : κ) => (t k : ℂ) * epsHom p i (Z k),
    Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun v _ => Finset.prod_mul_distrib

end Eps

/-! ### The weighted fluctuation average -/

/-- `∑_k t_k Z_k` with `Z_k = (1 - E_k)(G_{kk} - m)`, for real weights `t`. -/
noncomputable def flucAvg {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (t : Idx d (sz.L n) (sz.W n) → ℝ) : Sizes.SeqΩ sz → ℂ :=
  fun ω => ∑ k, (t k : ℂ) * flucDiag sz n u z m k ω

/-! ### The two coefficient families at `d ≥ 3`

The block of a site `k ∈ Z_{WL}^d` is `(split d L W k).1 ∈ Z_L^d`, the first component of
`splitEquiv`.  The row family is `j ↦ svarF d L W g i j` (the paper's `S_{ij}`), the block family
is `k ↦ W^{-d} 1(k ∈ 𝓘_a)` (the diagonal of `E_a`, `Def_matE`). -/

section Families

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- For a set `T` of blocks, the sites whose block lies in `T` number `#T · W^d` (the block fibre
is `Fin (W^d)`).  RBM2D `flucVanish_card_filter_blk2_mem` (`FlucVanish.lean:350`), where the
fibre is `Fin W × Fin W` and the count `#T · W²`. -/
theorem flucVanish_card_filter_blk_mem (T : Finset (Zd d L)) :
    ((univ : Finset (Idx d L W)).filter fun k => (split d L W k).1 ∈ T).card
      = T.card * W ^ d := by
  classical
  have h : ((univ : Finset (Idx d L W)).filter
      fun k => (split d L W k).1 ∈ T).map (splitEquiv d L W).toEmbedding
      = T ×ˢ (univ : Finset (Fin (W ^ d))) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_toEmbedding, Finset.mem_product, and_true]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hp
      refine ⟨(splitEquiv d L W).symm p, ?_, (splitEquiv d L W).apply_symm_apply p⟩
      have : (split d L W ((splitEquiv d L W).symm p)).1 = p.1 :=
        congrArg Prod.fst ((splitEquiv d L W).apply_symm_apply p)
      rw [this]
      exact hp
  rw [← Finset.card_map, h, Finset.card_product, Finset.card_univ, Fintype.card_fin]

/-- The set `{0} ∪ {x : |x|₁ = 1}`: the block itself and its `2d` nearest neighbours (`3 ≤ L`).
The kernel `sbKernelR d L g` of `S^(B)(g)` vanishes outside it (and, for `g ≠ 0`, is nonzero on
all of it).  RBM2D `sbSupport L` is the five-point set `{0, ±e₁, ±e₂}` (`Defs/Block.lean:48`):
the constant `5` becomes `2d + 1` (`flucVanish_card_sbSupport`). -/
def flucVanish_sbSupport (d L : ℕ) [NeZero L] : Finset (Zd d L) :=
  insert 0 (Finset.univ.filter fun x : Zd d L => zdistD d L x = 1)

theorem flucVanish_mem_sbSupport {x : Zd d L} :
    x ∈ flucVanish_sbSupport d L ↔ x = 0 ∨ zdistD d L x = 1 := by
  simp [flucVanish_sbSupport]

/-- For `3 ≤ L`, `flucVanish_sbSupport d L` has `2 d + 1` points (the paper's `a ∼ b`:
`2d` neighbours, `card_nbhd`); RBM2D `card_sbSupport` is `5 = 2·2 + 1`. -/
theorem flucVanish_card_sbSupport (hL : 3 ≤ L) :
    (flucVanish_sbSupport d L).card = 2 * d + 1 := by
  unfold flucVanish_sbSupport
  rw [Finset.card_insert_of_notMem, card_nbhd d L hL]
  simp

/-- The blocks `b` with `b - a ∈ flucVanish_sbSupport d L` are as many as the points of
`flucVanish_sbSupport d L`.  RBM2D `flucVanish_card_filter_sub_mem_sbSupport` (`:374`), where the
filter reads `a - b ∈ sbSupport L`; the orientation `b - a` is that of Amend 1 of T2061. -/
theorem flucVanish_card_filter_sub_mem_sbSupport (a : Zd d L) :
    ((univ : Finset (Zd d L)).filter fun b => b - a ∈ flucVanish_sbSupport d L).card
      = (flucVanish_sbSupport d L).card := by
  classical
  have hset : ((univ : Finset (Zd d L)).filter fun b => b - a ∈ flucVanish_sbSupport d L)
      = (flucVanish_sbSupport d L).image fun s => a + s := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    refine ⟨fun h => ⟨b - a, h, by abel⟩, ?_⟩
    rintro ⟨s, hs, rfl⟩
    simpa using hs
  rw [hset, Finset.card_image_of_injective _ fun x y h => add_left_cancel h]

/-- The support of the row `j ↦ svarF d L W g i j` has `#(flucVanish_sbSupport d L) · W^d` sites.
RBM2D `flucVanish_card_svarSupport` (`:400`). -/
theorem flucVanish_card_svarSupport (i : Idx d L W) :
    ((univ : Finset (Idx d L W)).filter fun j =>
        (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L).card
      = (flucVanish_sbSupport d L).card * W ^ d := by
  classical
  have hset : ((univ : Finset (Idx d L W)).filter fun j =>
        (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L)
      = (univ : Finset (Idx d L W)).filter fun j => (split d L W j).1 ∈
          (univ : Finset (Zd d L)).filter fun b =>
            b - (split d L W i).1 ∈ flucVanish_sbSupport d L := by
    ext j
    simp
  rw [hset, flucVanish_card_filter_blk_mem, flucVanish_card_filter_sub_mem_sbSupport]

/-- For `3 ≤ L` the row `j ↦ svarF d L W g i j` is supported on `(2d + 1) W^d` sites (RBM2D
`flucVanish_card_svarSupport_eq` (`:412`): `5 W²`).  The support `A` is the geometric set
`{j : blk j - blk i ∈ {0} ∪ nbhd}`; the row vanishes off it for every `g`, and is nonzero on all
of it iff `g ≠ 0`. -/
theorem flucVanish_card_svarSupport_eq (hL : 3 ≤ L) (i : Idx d L W) :
    ((univ : Finset (Idx d L W)).filter fun j =>
        (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L).card
      = (2 * d + 1) * W ^ d := by
  rw [flucVanish_card_svarSupport, flucVanish_card_sbSupport d L hL]

/-- A block has exactly `W^d` sites (RBM2D `flucVanish_card_blockSupport` (`:419`): `W²`). -/
theorem flucVanish_card_blockSupport (a : Zd d L) :
    ((univ : Finset (Idx d L W)).filter fun k => (split d L W k).1 = a).card
      = W ^ d := by
  classical
  have := flucVanish_card_filter_blk_mem d L W {a}
  simpa using this

/-- Each row of the variance profile sums to `1` (`3 ≤ L`): `∑_k S_{xk} = ∑_b S^{(B)}_{ab} = 1`
(`sum_sbKernelR`; the bridge `splitEquiv`).  Private copy of the private
`RBM.Green.sum_svarF_row` of `Green/RowIndep.lean`. -/
private theorem flucVanish_sum_svarF_row (g : ℝ) (hL : 3 ≤ L) (x : Idx d L W) :
    ∑ k : Idx d L W, svarF d L W g x k = 1 := by
  have h1 : ∑ k : Idx d L W, svarF d L W g x k
      = ∑ p : Vtx d L W, ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W x).1 p.1 :=
    Fintype.sum_equiv (splitEquiv d L W) _ _ fun k => rfl
  have h2 : ∑ b, SBR d L g (split d L W x).1 b = 1 := by
    rw [← sum_sbKernelR d L g hL]
    exact Fintype.sum_equiv (Equiv.subLeft (split d L W x).1) _ _ fun b => by simp [SBR]
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  calc ∑ a : Zd d L, ((W : ℝ) ^ d) * (((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W x).1 a)
      = ∑ a : Zd d L, SBR d L g (split d L W x).1 a :=
        Finset.sum_congr rfl fun a _ => by rw [← mul_assoc, mul_inv_cancel₀ hW, one_mul]
    _ = 1 := h2

/-- The entries of `S^(B)(g)` are at most `1` (`3 ≤ L`): a single term of the row sum
`sum_sbKernelR`. -/
private theorem flucVanish_sbKernelR_le_one (g : ℝ) (hL : 3 ≤ L) (x : Zd d L) :
    sbKernelR d L g x ≤ 1 :=
  calc sbKernelR d L g x ≤ ∑ y, sbKernelR d L g y :=
        Finset.single_le_sum (f := fun y => sbKernelR d L g y)
          (fun y _ => sbKernelR_nonneg d L g y) (Finset.mem_univ x)
    _ = 1 := sum_sbKernelR d L g hL

/-- **The variance-profile row `t_j = S_{ij} = svarF d L W g i j`** is a bounded weight
(Amend 1 of T2061, DECISIONS §30; paper-delta candidate `T2061a`): `0 ≤ t_j ≤ W^{-d}` on the sites
`j` whose block is `b_i` or one of its `2d` neighbours (`(2d + 1) W^d` sites,
`flucVanish_card_svarSupport_eq`), `t_j = 0` elsewhere, and `∑_j t_j = 1`.  RBM2D
`uniformWeight_svar` (`:428`) is **false** at `d ≥ 3` as ported: `t` takes the two nonzero values
`W^{-d}(1 + 2dg²)⁻¹` and `g² W^{-d}(1 + 2dg²)⁻¹` on `A`. -/
theorem boundedWeight_svarF (hL : 3 ≤ L) (g : ℝ) (i : Idx d L W) :
    BoundedWeight (fun j : Idx d L W => svarF d L W g i j) (((W : ℝ) ^ d)⁻¹)
      ((univ : Finset (Idx d L W)).filter fun j =>
        (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L) := by
  classical
  have hsv : ∀ j : Idx d L W, svarF d L W g i j
      = ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g ((split d L W i).1 - (split d L W j).1) :=
    fun j => rfl
  refine ⟨by positivity, fun j => svarF_nonneg d L W g i j, fun j _ => ?_, fun j hj => ?_,
    (flucVanish_sum_svarF_row d L W g hL i).le⟩
  · rw [hsv]
    calc ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g ((split d L W i).1 - (split d L W j).1)
        ≤ ((W : ℝ) ^ d)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (flucVanish_sbKernelR_le_one d L g hL _) (by positivity)
      _ = ((W : ℝ) ^ d)⁻¹ := mul_one _
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, flucVanish_mem_sbSupport,
      not_or] at hj
    rw [hsv, ← neg_sub, sbKernelR_neg]
    unfold sbKernelR
    rw [ite_eq_right hj.1, ite_eq_right hj.2]
    simp

/-- **The row `j ↦ S_{ij}` is not a uniform weight at `d ≥ 1`, `g² ≠ 1`** (the reason for Amend 1
of T2061, DECISIONS §30): on the support `A` of `boundedWeight_svarF` the row takes the two values
`W^{-d}(1 + 2dg²)⁻¹` (same block, `j = i`) and `g² W^{-d}(1 + 2dg²)⁻¹` (a neighbouring block), which
differ unless `g² = 1`.  RBM2D's five-point profile has no `g`, so there the row is uniform
(`uniformWeight_svar`, `FlucVanish.lean:428`). -/
theorem not_uniformWeight_svarF (hd : 0 < d) (hL : 3 ≤ L) {g : ℝ} (hg1 : g ^ 2 ≠ 1)
    (i : Idx d L W) (c : ℝ) :
    ¬ UniformWeight (fun j : Idx d L W => svarF d L W g i j) c
      ((univ : Finset (Idx d L W)).filter fun j =>
        (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L) := by
  classical
  intro h
  set a : Zd d L := (split d L W i).1 with ha
  set e : Zd d L := unitVec d L (⟨0, hd⟩, true) with he
  have he1 : zdistD d L e = 1 := zdistD_unitVec hL _
  have he0 : e ≠ 0 := fun h0 => by rw [h0, zdistD_zero] at he1; exact absurd he1 (by decide)
  have hW0 : NeZero (W ^ d) := inferInstance
  set j1 : Idx d L W := (splitEquiv d L W).symm (a + e, 0) with hj1def
  have hj1 : (split d L W j1).1 = a + e :=
    congrArg Prod.fst ((splitEquiv d L W).apply_symm_apply (a + e, 0))
  have hmem0 : i ∈ ((univ : Finset (Idx d L W)).filter fun j =>
      (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L) := by
    simp [flucVanish_mem_sbSupport]
  have hmem1 : j1 ∈ ((univ : Finset (Idx d L W)).filter fun j =>
      (split d L W j).1 - (split d L W i).1 ∈ flucVanish_sbSupport d L) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, flucVanish_mem_sbSupport, hj1,
      ← ha, add_sub_cancel_left]
    exact Or.inr he1
  have v0 := h.mem i hmem0
  have v1 := h.mem j1 hmem1
  rw [svarF_diag] at v0
  have hv1 : svarF d L W g i j1
      = ((W : ℝ) ^ d)⁻¹ * (g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹) := by
    have : svarF d L W g i j1
        = ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g (a - (a + e)) := by
      change ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j1).1 = _
      rw [hj1]; rfl
    rw [this, show a - (a + e) = -e by abel, sbKernelR_neg]
    unfold sbKernelR
    rw [ite_eq_right he0, ite_eq_left he1]
    simp
  rw [hv1] at v1
  have hpos : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  have hWpos : (0 : ℝ) < ((W : ℝ) ^ d)⁻¹ := by
    have : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  have heq : ((W : ℝ) ^ d)⁻¹ * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹
      = ((W : ℝ) ^ d)⁻¹ * (g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹) := v0.trans v1.symm
  have h2 := mul_left_cancel₀ hWpos.ne' heq
  field_simp at h2
  exact hg1 h2.symm

/-- **The block average `t_k = W^{-d} · 1(k ∈ 𝓘_a)`** is a uniform weight, with weight `W^{-d}` on
the `W^d` sites of block `a` (RBM2D `uniformWeight_blockAvg2` (`:456`): `W⁻²`, `W²`). -/
theorem uniformWeight_blockAvg2 (a : Zd d L) :
    UniformWeight
      (fun k : Idx d L W => if (split d L W k).1 = a then ((W : ℝ) ^ d)⁻¹ else 0)
      (((W : ℝ) ^ d)⁻¹)
      ((univ : Finset (Idx d L W)).filter fun k => (split d L W k).1 = a) := by
  classical
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  refine ⟨by positivity, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · simp [(Finset.mem_filter.1 hk).2]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    simp [hk]
  · rw [flucVanish_card_blockSupport]
    push_cast
    rw [inv_mul_cancel₀ hW]

/-- The block-average weight is `blkCoef2` read through `splitEquiv` (RBM2D
`flucVanish_blockAvg2_eq_blkCoef2` (`:472`); `blkCoef2` of `Green/EntryDom.lean`). -/
theorem flucVanish_blockAvg2_eq_blkCoef2 (a : Zd d L) (k : Idx d L W) :
    (if (split d L W k).1 = a then ((W : ℝ) ^ d)⁻¹ else 0)
      = blkCoef2 d L W a (splitEquiv d L W k) := by
  rfl

end Families


/-! ### The diagonal Green function never vanishes off the real axis

Private port of RBM2D `Green/LDE.lean:35-100` (`im_green_diag`, `green_diag_ne_zero`,
commit `c9a24cf`), used only to discharge the side condition `G_{kk} ≠ 0` of
`greenMinorMat_eq_minorGreen` in the instance below at every sample point. -/

section GreenDiag

open scoped ComplexOrder

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

private theorem flucVanish_isUnit_det {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det :=
  (Matrix.isUnit_iff_isUnit_det _).1 (RBM.isUnit_sub_smul_of_isHermitian hH hz)

/-- **The Ward identity at one site**: `Im G_{ii} = Im z · ‖G e_i‖²`. -/
private theorem flucVanish_im_green_diag {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (i : ν) :
    (green H z i i).im
      = z.im * (star (green H z *ᵥ Pi.single i 1) ⬝ᵥ (green H z *ᵥ Pi.single i 1)).re := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := flucVanish_isUnit_det hH hz
  set v : ν → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hvi : v i = green H z i i := by
    rw [hv]; simp
  have hMv : (H - z • (1 : Matrix ν ν ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hsplit : star v ⬝ᵥ ((H - z • (1 : Matrix ν ν ℂ)) *ᵥ v)
      = star v ⬝ᵥ (H *ᵥ v) - z * (star v ⬝ᵥ v) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  rw [hMv, dotProduct_single_one] at hsplit
  have hHim : (star v ⬝ᵥ H *ᵥ v).im = 0 := by
    simpa [RCLike.im_to_complex] using hH.im_star_dotProduct_mulVec_self v
  have hself : (star v ⬝ᵥ v).im = 0 := by
    have := dotProduct_star_self_nonneg v
    rw [Complex.le_def] at this
    exact this.2.symm
  have := congrArg Complex.im hsplit
  rw [Complex.sub_im, hHim, Complex.mul_im, hself] at this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_im, hvi] at this
  linarith [this]

/-- **`G_{ii} ≠ 0`.**  For Hermitian `H` and `Im z ≠ 0` the diagonal Green function is never
zero. -/
private theorem flucVanish_green_diag_ne_zero {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) (i : ν) : green H z i i ≠ 0 := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det := flucVanish_isUnit_det hH hz
  set v : ν → ℂ := green H z *ᵥ Pi.single i 1 with hv
  have hMv : (H - z • (1 : Matrix ν ν ℂ)) *ᵥ v = Pi.single i 1 := by
    rw [hv, Matrix.mulVec_mulVec, self_mul_green hdet, Matrix.one_mulVec]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero] at hMv
    have h1 := congrFun hMv i
    simp at h1
  have hpos : (0 : ℂ) < star v ⬝ᵥ v := dotProduct_star_self_pos_iff.2 hvne
  rw [Complex.lt_def] at hpos
  have hre : (0 : ℝ) < (star v ⬝ᵥ v).re := by simpa using hpos.1
  intro hzero
  have him := flucVanish_im_green_diag hH hz i
  rw [hzero] at him
  simp only [Complex.zero_im] at him
  have : z.im = 0 := by
    rcases mul_eq_zero.1 him.symm with h | h
    · exact h
    · exact absurd h (ne_of_gt hre)
  exact hz this

end GreenDiag


namespace FlucVanishInst

/-! ### Compiled nonempty instances at the preflight sequence `sz0` (`d = 3`)

`SizesInst.sz0` (`RBM3D/Defs/Sizes.lean:260`) at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`,
`N = (W L)^3 = 2097152`, block size `W^d = 32768`.  Every deterministic hypothesis of the theorems
below is discharged at every sample point; there is no external hypothesis.  The lemmas that
name `IsRowCoord` at concrete sizes are checked at the sizes `szS` instead (see below). -/

open RBM.Gauss RBM.Gauss.SizesInst
open scoped Matrix.Norms.L2Operator

/-- The spectral parameter `z = 1/2 + i/2` of the instances: `Im z = 1/2 ≠ 0`. -/
private noncomputable def zI : ℂ := (1 / 2 : ℂ) + Complex.I / 2

private theorem zI_im : zI.im ≠ 0 := by
  norm_num [zI]

/-! #### Target `greenMinorMat_eq_minorGreen` -/

/-- **Instance of `greenMinorMat_eq_minorGreen`** at `sz0`, `n = 0`, `u = 1/2`, `z = 1/2 + i/2`,
row `k = 0`, at every sample point `ω`: `IsUnit det(H_u - z)` and `G_{kk} ≠ 0` hold for every
Hermitian `H` off the real axis (`RBM.isUnit_sub_smul_of_isHermitian`, the Ward identity), so the
theorem applies with no hypothesis left. -/
theorem greenMinorMat_eq_minorGreen_sz0 (ω : Sizes.SeqΩ sz0) :
    greenMinorMat sz0 0 (1 / 2) zI (0 : Idx 3 (sz0.L 0) (sz0.W 0)) ω
      = minorGreen (green (Sizes.seqHflow sz0 0 (1 / 2) ω) zI) 0 :=
  greenMinorMat_eq_minorGreen sz0 0 (1 / 2) zI 0 ω
    (flucVanish_isUnit_det (Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω) zI_im)
    (flucVanish_green_diag_ne_zero (Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω) zI_im 0)

/-- The minor resolvent is `FinDepOffRow` at `sz0` (`finDepOffRow_greenMinorMat`), hence its own
`E_0` (`condRow_of_finDepOffRow`), entry by entry. -/
theorem condRow_greenMinorMat_apply_sz0
    (a b : {a : Idx 3 (sz0.L 0) (sz0.W 0) // a ≠ 0}) :
    condRow sz0 0 (0 : Idx 3 (sz0.L 0) (sz0.W 0))
        (fun ω => greenMinorMat sz0 0 (1 / 2) zI 0 ω a b)
      = fun ω => greenMinorMat sz0 0 (1 / 2) zI 0 ω a b :=
  condRow_of_finDepOffRow (finDepOffRow_greenMinorMat_apply sz0 0 (1 / 2) zI 0 a b)

/-! #### The row-conditioning lemmas, at the small sizes `d = 3`, `L = 3`, `W = 1`

`IsRowCoord szS ..` unfolds (by whnf) to a membership in an explicit finite set of coordinates;
at `sz0` (`N = 2097152`) Lean's unifier would evaluate that set (maximum recursion depth), so the
checks of `condRow`, `FinDepOffRow` and the vanishing lemma use the sizes `szS` (`27` sites), as the
RBM2D checks use `L = 3`, `W = 1`.  The key target `greenMinorMat_eq_minorGreen` and everything
that does not name `IsRowCoord` at concrete sizes is at `sz0` above. -/

/-- The sizes `d = 3`, `L n = 3`, `W n = 1` for every `n` (`27` sites). -/
private def szS : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 1
  lam := fun _ => 1
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => Nat.one_pos

/-- The coordinate `⟨0, 0, 0, true⟩` of slice `0`: the real part of `H_00` (a row-`0`
coordinate). -/
private noncomputable def c0 : Sizes.SeqCoord szS := ⟨0, 0, 0, true⟩

private noncomputable def X0 (ω : Sizes.SeqΩ szS) : ℂ :=
  Complex.exp ((ω c0 : ℂ) * Complex.I)

private theorem X0_measurable : Measurable X0 :=
  Measurable.cexp
    ((Complex.measurable_ofReal.comp (measurable_pi_apply c0)).mul_const Complex.I)

private theorem X0_norm (ω : Sizes.SeqΩ szS) : ‖X0 ω‖ ≤ 1 :=
  (Complex.norm_exp_ofReal_mul_I _).le

private theorem c0_isRowCoord :
    IsRowCoord szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) c0 :=
  (isRowCoord_mk szS 0 0 0 0 true).2 (Or.inl rfl)

/-- `X₀` reads a row-`0` coordinate, so it is not `FinDepOffRow`: the hypotheses of
`condRow_of_finDepOffRow` are not vacuous. -/
theorem X0_not_finDepOffRow_szS :
    ¬ FinDepOffRow szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) X0 := by
  classical
  rintro ⟨I, hI, h⟩
  have h0 : c0 ∉ I := fun hc => hI _ hc c0_isRowCoord
  have key := h 0 (Function.update 0 c0 (Real.pi / 2)) fun c hc => by
    have hne : c ≠ c0 := fun hcc => h0 (hcc ▸ hc)
    exact (Function.update_of_ne hne _ _).symm
  simp only [X0, Pi.zero_apply, Function.update_self, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, Complex.ofReal_div, Complex.ofReal_ofNat] at key
  rw [Complex.exp_pi_div_two_mul_I] at key
  have him := congrArg Complex.im key
  simp at him

/-- **Instance of `condRow_sub_condRow`** (`E_0 (1 - E_0) = 0`) at `szS`, `X₀ = exp (i ω(c₀))`. -/
theorem condRow_sub_condRow_szS :
    condRow szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) (fun ω => X0 ω - condRow szS 0 0 X0 ω) = 0 :=
  condRow_sub_condRow 0 (rowIntegrable_of_measurable_of_bound X0_measurable X0_norm)

/-- **Instance of `integral_condRow`** (`E[E_0 X] = E[X]`) at `szS`, `X₀ = exp (i ω(c₀))`. -/
theorem integral_condRow_szS :
    ∫ ω, condRow szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) X0 ω ∂(Sizes.seqP szS)
      = ∫ ω, X0 ω ∂(Sizes.seqP szS) :=
  integral_condRow 0
    (integrable_P_of_measurable_of_bound X0_measurable X0_norm)

/-- `E_0 X₀` is the constant `E X₀` (`c₀` is a row-`0` coordinate, so `X₀ ∘ rowSplit` is `X₀`
of the second argument). -/
private theorem condRow_X0 :
    condRow szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) X0
      = fun _ => ∫ ω', X0 ω' ∂(Sizes.seqP szS) := by
  funext ω
  have : ∀ ω' : Sizes.SeqΩ szS, X0 (rowSplit szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) ω ω') = X0 ω' :=
    fun ω' => by
      simp only [X0, rowSplit_apply_of_isRowCoord 0 ω ω' c0_isRowCoord]
  simp only [condRow_apply, this]

/-- **Instance of the vanishing lemma `integral_mul_prod_eq_zero`** at `szS`: two slots
`ι = Fin 2`, distinguished slot `0` with `Z₀ = X₀ - E_0 X₀` (killed by `E_0`,
`condRow_sub_condRow`), the other factor the constant `1` (`finDepOffRow_const`); the integrand is
bounded and measurable, hence integrable.  Conclusion: `E (X₀ - E X₀) = 0`. -/
theorem integral_mul_prod_eq_zero_szS :
    ∫ ω, (X0 ω - condRow szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) X0 ω) *
        ∏ _i ∈ (Finset.univ : Finset (Fin 2)).erase 0, (fun _ : Sizes.SeqΩ szS => (1 : ℂ)) ω
      ∂(Sizes.seqP szS) = 0 := by
  have hmeas : Measurable fun ω => (X0 ω - condRow szS 0 (0 : Idx 3 (szS.L 0) (szS.W 0)) X0 ω) *
      ∏ _i ∈ (Finset.univ : Finset (Fin 2)).erase 0, (fun _ : Sizes.SeqΩ szS => (1 : ℂ)) ω := by
    rw [condRow_X0]
    simp only [Finset.prod_const_one, mul_one]
    exact X0_measurable.sub measurable_const
  refine integral_mul_prod_eq_zero (sz := szS) (n := 0) (κ := 0) (i₀ := (0 : Fin 2))
    (Z := fun _ ω => X0 ω - condRow szS 0 0 X0 ω)
    (Y := fun _ _ => (1 : ℂ)) (condRow_sub_condRow 0
      (rowIntegrable_of_measurable_of_bound X0_measurable X0_norm))
    (fun i _ => finDepOffRow_const 0 _) ?_
  refine Integrable.mono' (integrable_const (2 : ℝ)) hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [condRow_X0]
  simp only [Finset.prod_const_one, mul_one]
  have hm : ‖∫ ω', X0 ω' ∂(Sizes.seqP szS)‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := Sizes.seqP szS) (f := X0) (C := 1)
      (Filter.Eventually.of_forall X0_norm)
  calc ‖X0 ω - ∫ ω', X0 ω' ∂(Sizes.seqP szS)‖
      ≤ ‖X0 ω‖ + ‖∫ ω', X0 ω' ∂(Sizes.seqP szS)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (X0_norm ω) hm
    _ = 2 := by norm_num

/-- **Instance of `norm_flucDiag_le`** at `sz0`: `‖Z_0‖ ≤ 2 |Im z|⁻¹` for `m = 0`, every `ω`
(`‖G_{00}‖ ≤ |Im z|⁻¹`, `norm_inverse_entry_le`). -/
theorem norm_flucDiag_le_sz0 (ω : Sizes.SeqΩ sz0) :
    ‖flucDiag sz0 0 (1 / 2) zI 0 (0 : Idx 3 (sz0.L 0) (sz0.W 0)) ω‖ ≤ 2 * |zI.im|⁻¹ :=
  norm_flucDiag_le (fun ω' => by
    have h := norm_inverse_entry_le (Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω') zI_im 0 0
    simpa [greenDiagCentered, green, Matrix.nonsing_inv_eq_ringInverse] using h) ω

/-! #### Target `continuous_green_comp` and the coordinate calculus -/

/-- **Instance of `continuous_green_comp`** at `sz0`, `V = ℝ` (the time `u`), fixed sample `ω`,
`z = 1/2 + i/2`: `u ↦ G_u` is continuous.  The hypotheses (`u ↦ H_u` continuous, Hermitian,
`Im z ≠ 0`) are discharged. -/
theorem continuous_green_comp_sz0_time (ω : Sizes.SeqΩ sz0) :
    Continuous fun u : ℝ => green (Sizes.seqHflow sz0 0 u ω) zI :=
  continuous_green_comp (Sizes.continuous_seqHflow_time sz0 0 ω)
    (fun u => Sizes.seqHflow_isHermitian sz0 0 u ω) zI_im

/-- **Instance of `continuous_green_comp`** at `sz0`, `V = Sizes.SeqΩ sz0` (the sample), fixed
time `u = 1/2`: `ω ↦ G` is continuous in the Gaussian coordinates. -/
theorem continuous_green_comp_sz0_sample :
    Continuous fun ω : Sizes.SeqΩ sz0 => green (Sizes.seqHflow sz0 0 (1 / 2) ω) zI :=
  continuous_green_comp (GreenDeriv_continuous_seqHflow sz0 0 (1 / 2))
    (fun ω => Sizes.seqHflow_isHermitian sz0 0 (1 / 2) ω) zI_im

/-- **Instance of `Xmat_eq_sum`** at `d = 3`, `L = 4`, `W = 32`. -/
theorem Xmat_eq_sum_sz0 (ω : Ω 3 4 32) :
    Xmat 3 4 32 ω = ∑ c ∈ usedCoords 3 4 32, ω c • Bmat 3 4 32 c.1 c.2.1 c.2.2 :=
  Xmat_eq_sum 3 4 32 ω

/-- **Instance of `hasFDerivAt_resH`** at the base point `H_{1/2}(ω)` of `sz0`. -/
theorem hasFDerivAt_resH_sz0 (ω : Sizes.SeqΩ sz0) :
    HasFDerivAt (resH (n := Idx 3 (sz0.L 0) (sz0.W 0)) zI)
      (-((ContinuousLinearMap.mulLeftRight ℝ
          (Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
          (resH zI (Sizes.seqHflow sz0 0 (1 / 2) ω))
          (resH zI (Sizes.seqHflow sz0 0 (1 / 2) ω))).comp
        (hermCLM (Idx 3 (sz0.L 0) (sz0.W 0))))) (Sizes.seqHflow sz0 0 (1 / 2) ω) :=
  hasFDerivAt_resH zI_im _

/-- **Instance of `finDep_of_Hflow`** at `sz0`: `ω ↦ G_{00} - m` reads finitely many
coordinates. -/
theorem finDep_of_Hflow_sz0 :
    FinDep sz0 fun ω => green (Sizes.seqHflow sz0 0 (1 / 2) ω) zI 0 0 - 0 :=
  finDep_of_Hflow sz0 0 (1 / 2) fun M => green M zI 0 0 - 0

/-! #### Target `flucVanish_blockAvg2_eq_blkCoef2` and the weights -/

/-- **Instance of `flucVanish_blockAvg2_eq_blkCoef2`** at `d = 3`, `L = 4`, `W = 32`, block
`a = 0`, every site `k`; with the block of the site `0` (`32768 = W^d` sites of weight `W^{-d}`,
the window is not collapsed). -/
theorem flucVanish_blockAvg2_eq_blkCoef2_sz0 (k : Idx 3 (sz0.L 0) (sz0.W 0)) :
    (if (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0 then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0)
      = blkCoef2 3 (sz0.L 0) (sz0.W 0) 0 (splitEquiv 3 (sz0.L 0) (sz0.W 0) k) :=
  flucVanish_blockAvg2_eq_blkCoef2 3 (sz0.L 0) (sz0.W 0) 0 k

/-- Nondegeneracy of the previous instance: the block `0` has `32768` sites and the weight at the
site `0` is `1/32768 ≠ 0`. -/
theorem flucVanish_blockAvg2_nondegenerate_sz0 :
    ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun k =>
        (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0).card = 32768 ∧
      blkCoef2 3 (sz0.L 0) (sz0.W 0) 0 (splitEquiv 3 (sz0.L 0) (sz0.W 0) 0) = 1 / 32768 := by
  refine ⟨?_, ?_⟩
  · rw [flucVanish_card_blockSupport]
    norm_num [sz0]
  · rw [← flucVanish_blockAvg2_eq_blkCoef2]
    have h0 : (split 3 (sz0.L 0) (sz0.W 0) 0).1 = 0 := by
      funext i
      simp [split, blk]
    rw [ite_eq_left h0]
    norm_num [sz0]

/-- **Instance of `uniformWeight_blockAvg2`** at `sz0`, block `0`. -/
theorem uniformWeight_blockAvg2_sz0 :
    UniformWeight
      (fun k : Idx 3 (sz0.L 0) (sz0.W 0) =>
        if (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0 then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0)
      ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹)
      ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun k =>
        (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0) :=
  uniformWeight_blockAvg2 3 (sz0.L 0) (sz0.W 0) 0

/-- **Instance of `UniformWeight.toBoundedWeight`** at `sz0`: the block average is a bounded
weight. -/
theorem boundedWeight_blockAvg2_sz0 :
    BoundedWeight
      (fun k : Idx 3 (sz0.L 0) (sz0.W 0) =>
        if (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0 then (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ else 0)
      ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹)
      ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun k =>
        (split 3 (sz0.L 0) (sz0.W 0) k).1 = 0) :=
  uniformWeight_blockAvg2_sz0.toBoundedWeight

/-- **Instance of `boundedWeight_svarF`** at `sz0` (`g = sz0.lam 0 = 1/64`, `L = 4`), row `i = 0`:
the row `j ↦ S_{0j}` is a bounded weight with `c = W^{-d}` on the `(2d + 1) W^d` sites of the
block `0` and its six neighbours. -/
theorem boundedWeight_svarF_sz0 :
    BoundedWeight
      (fun j : Idx 3 (sz0.L 0) (sz0.W 0) =>
        svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j)
      ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹)
      ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun j =>
        (split 3 (sz0.L 0) (sz0.W 0) j).1 - (split 3 (sz0.L 0) (sz0.W 0) 0).1
          ∈ flucVanish_sbSupport 3 (sz0.L 0)) :=
  boundedWeight_svarF 3 (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) (sz0.lam 0) 0

/-- Nondegeneracy of the previous instance: the support has `(2d + 1) W^d = 229376` sites. -/
theorem boundedWeight_svarF_card_sz0 :
    ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun j =>
        (split 3 (sz0.L 0) (sz0.W 0) j).1 - (split 3 (sz0.L 0) (sz0.W 0) 0).1
          ∈ flucVanish_sbSupport 3 (sz0.L 0)).card = 229376 := by
  rw [flucVanish_card_svarSupport_eq 3 (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0)]
  norm_num [sz0]

/-- **The uniform form fails at `sz0`** (the negative statement behind Amend 1): `g = 1/64`, so
`g² ≠ 1`, and the row `j ↦ S_{0j}` is not a `UniformWeight` for any constant `c`. -/
theorem not_uniformWeight_svarF_sz0 (c : ℝ) :
    ¬ UniformWeight
      (fun j : Idx 3 (sz0.L 0) (sz0.W 0) =>
        svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) 0 j) c
      ((Finset.univ : Finset (Idx 3 (sz0.L 0) (sz0.W 0))).filter fun j =>
        (split 3 (sz0.L 0) (sz0.W 0) j).1 - (split 3 (sz0.L 0) (sz0.W 0) 0).1
          ∈ flucVanish_sbSupport 3 (sz0.L 0)) :=
  not_uniformWeight_svarF 3 (sz0.L 0) (sz0.W 0) (by norm_num) (sz0.three_le_L 0)
    (by norm_num [sz0]) 0 c

end FlucVanishInst

end RBM.Green
