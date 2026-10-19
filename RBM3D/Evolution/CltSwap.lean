/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.FineModel

/-!
# The independent copy and the partial replacement on the one-size Gaussian model

On the finite product model `PF d L W g` over the `2 (W L)^{2d}` real coordinates of
`CoordF d L W` (the variance parameter `g` enters wherever `PF` occurs) this file gives

* the coordinate split `cltSplit S ω ω'` (coordinates in `S` from `ω'`, the others from `ω`) and
  the fact that `(ω, ω') ↦ cltSplit S ω ω'` pushes `PF ⊗ PF` to `PF`
  (`measurePreserving_cltSplit`; pattern: `measurePreserving_rowSplit`,
  `RBM3D/Green/FlucVanish.lean`);
* the hybrids `cltHyb e k` and the telescoping sum `cltTelescope`;
* the one-coordinate exchange `cltSwap c` and the fact that it preserves `PF ⊗ PF`
  (`measurePreserving_cltSwap`), and its consequence that an antisymmetric integrand integrates
  to zero (`integral_eq_zero_of_cltSwap_neg`);
* the transfer `cltTransfer` from `Sizes.seqP sz` to `PF d (sz.L n) (sz.W n) (sz.lam n)`.

This is the first brick of the proof of `STCltIso` (`(eq:bound_isolated)`, which
cites [DYYY25, (7.39)]).  The paper (arXiv:2507.20274) does not contain this argument: the i.i.d.
copy `H'` and the coordinate exchange are not in the paper; the exchange replaces the vanishing of
the `H'` term in the cited argument of [DYYY25].  No hypothesis on `g` is used (`g` enters only
through `PF`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory RBM RBM.Gauss
open scoped NNReal ENNReal

section Rep

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The coordinate-wise switch: coordinates in `S` from `ω'`, the others from `ω`.  With
`(ω, ω') ∼ P ⊗ P`, `ω'` plays the role of the i.i.d. copy `H'` of the cited argument of
[DYYY25]. -/
def cltSplit (S : Finset (CoordF d L W)) (ω ω' : Ω d L W) : Ω d L W :=
  fun c => if c ∈ S then ω' c else ω c

/-- **The law of a hybrid** (`H'` an i.i.d. copy in the cited argument of [DYYY25]).  For every
set of coordinates `S`, `(ω, ω') ↦ cltSplit S ω ω'` pushes `P ⊗ P` to `P`.  Pattern: the
`measurePreserving_rowSplit` of `RBM3D/Green/FlucVanish.lean` with its row predicate replaced by
`S`.  Consumers: `CltStep` (the events of `CltGmaxWhpOf`, `CltFarEntryWhpOf` at the hybrid
`cltHyb e k`). -/
def MeasurePreservingCltSplit : Prop :=
  ∀ S : Finset (CoordF d L W),
    MeasurePreserving (fun p : Ω d L W × Ω d L W => cltSplit d L W S p.1 p.2)
      ((PF d L W g).prod (PF d L W g)) (PF d L W g)

/-- The first `k` coordinates in the enumeration `e`. -/
def cltHybSet (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (k : ℕ) : Finset (CoordF d L W) :=
  Finset.univ.filter fun c => ((e c : ℕ) < k)

/-- The hybrid `T_k`: the first `k` coordinates (in the enumeration `e`) replaced by those of
`ω'`.  `T_0 = ω`, `T_{card} = ω'` (`cltHyb_zero`, `cltHyb_card`). -/
def cltHyb (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (k : ℕ) (ω ω' : Ω d L W) : Ω d L W :=
  cltSplit d L W (cltHybSet d L W e k) ω ω'

/-- **Telescoping.**  For every `Φ : Ω → ℂ`, `Φ ω - Φ ω' = Σ_{k < card} (Φ T_k - Φ T_{k+1})`.  The
paper sums over the entries `i ≤ j`; here over the `card (CoordF d L W) = 2 N²` real
coordinates.  Proved: `cltTelescope`. -/
def CltTelescope : Prop :=
  ∀ (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (Φ : Ω d L W → ℂ) (ω ω' : Ω d L W),
    Φ ω - Φ ω' = ∑ k ∈ Finset.range (Fintype.card (CoordF d L W)),
      (Φ (cltHyb d L W e k ω ω') - Φ (cltHyb d L W e (k + 1) ω ω'))

theorem cltHyb_zero (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (ω ω' : Ω d L W) :
    cltHyb d L W e 0 ω ω' = ω := by
  funext c
  simp [cltHyb, cltSplit, cltHybSet]

theorem cltHyb_card (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (ω ω' : Ω d L W) :
    cltHyb d L W e (Fintype.card (CoordF d L W)) ω ω' = ω' := by
  funext c
  have hc := (e c).isLt
  simp only [cltHyb, cltSplit, cltHybSet, Finset.mem_filter, Finset.mem_univ, true_and, hc,
    ite_true]

theorem cltTelescope : CltTelescope d L W := by
  intro e Φ ω ω'
  rw [Finset.sum_range_sub' (fun k => Φ (cltHyb d L W e k ω ω')), cltHyb_zero, cltHyb_card]

private theorem cltSwap_cltHyb_ne (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) {k : ℕ}
    (hk : k < Fintype.card (CoordF d L W)) {c : CoordF d L W} (h : c ≠ e.symm ⟨k, hk⟩) :
    (e c : ℕ) ≠ k := by
  intro h'
  apply h
  rw [Equiv.eq_symm_apply]
  exact Fin.ext h'

/-- `T_{k+1} = update T_k c_k (ω' c_k)` with `c_k = e.symm k` (the step `Δ` of the cited argument, for one real coordinate). -/
theorem cltHyb_succ (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (k : ℕ)
    (hk : k < Fintype.card (CoordF d L W)) (ω ω' : Ω d L W) :
    cltHyb d L W e (k + 1) ω ω' =
      Function.update (cltHyb d L W e k ω ω') (e.symm ⟨k, hk⟩) (ω' (e.symm ⟨k, hk⟩)) := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet]
  · have hne := cltSwap_cltHyb_ne d L W e hk h
    rw [Function.update_of_ne h]
    simp only [cltHyb, cltSplit, cltHybSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- `T_k = update T_{k+1} c_k (ω c_k)`. -/
theorem cltHyb_eq_update_succ (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (k : ℕ)
    (hk : k < Fintype.card (CoordF d L W)) (ω ω' : Ω d L W) :
    cltHyb d L W e k ω ω' =
      Function.update (cltHyb d L W e (k + 1) ω ω') (e.symm ⟨k, hk⟩) (ω (e.symm ⟨k, hk⟩)) := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet]
  · have hne := cltSwap_cltHyb_ne d L W e hk h
    rw [Function.update_of_ne h]
    simp only [cltHyb, cltSplit, cltHybSet, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- The one-coordinate exchange `σ_c(ω, ω') = (update ω c (ω' c), update ω' c (ω c))`. -/
def cltSwap (c : CoordF d L W) (p : Ω d L W × Ω d L W) : Ω d L W × Ω d L W :=
  (Function.update p.1 c (p.2 c), Function.update p.2 c (p.1 c))

/-- **The exchange preserves `P ⊗ P`.**  The paper has no such statement; it replaces the vanishing of
the `H'` term of the cited argument.  Consumers: `IntegralEqZeroOfCltSwapNeg`, `CltStep`. -/
def MeasurePreservingCltSwap : Prop :=
  ∀ c : CoordF d L W,
    MeasurePreserving (cltSwap d L W c) ((PF d L W g).prod (PF d L W g)) ((PF d L W g).prod (PF d L W g))

/-- **Antisymmetric integrands integrate to zero** (a consequence of the previous statement, since
`cltSwap c` is an involution, hence a measurable equivalence).  No measurability or boundedness
hypothesis is needed: `∫ F = ∫ F ∘ σ_c = -∫ F`.  Consumer: `CltStep`. -/
def IntegralEqZeroOfCltSwapNeg : Prop :=
  ∀ (c : CoordF d L W) (F : Ω d L W × Ω d L W → ℂ), (∀ p, F (cltSwap d L W c p) = -F p) →
    ∫ p, F p ∂((PF d L W g).prod (PF d L W g)) = 0

/-- The exchange at `c_k` maps `T_k` to `T_{k+1}` (the case of `CltStep` that uses the exchange). -/
theorem cltHyb_cltSwap (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (k : ℕ)
    (hk : k < Fintype.card (CoordF d L W)) (p : Ω d L W × Ω d L W) :
    cltHyb d L W e k (cltSwap d L W (e.symm ⟨k, hk⟩) p).1 (cltSwap d L W (e.symm ⟨k, hk⟩) p).2 =
      cltHyb d L W e (k + 1) p.1 p.2 := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet, cltSwap]
  · have hne := cltSwap_cltHyb_ne d L W e hk h
    simp only [cltHyb, cltSplit, cltHybSet, cltSwap, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.update_of_ne h]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- The exchange at `c_k` maps `T_{k+1}` to `T_k`. -/
theorem cltHyb_succ_cltSwap (e : CoordF d L W ≃ Fin (Fintype.card (CoordF d L W))) (k : ℕ)
    (hk : k < Fintype.card (CoordF d L W)) (p : Ω d L W × Ω d L W) :
    cltHyb d L W e (k + 1) (cltSwap d L W (e.symm ⟨k, hk⟩) p).1 (cltSwap d L W (e.symm ⟨k, hk⟩) p).2 =
      cltHyb d L W e k p.1 p.2 := by
  funext c
  by_cases h : c = e.symm ⟨k, hk⟩
  · subst h
    simp [cltHyb, cltSplit, cltHybSet, cltSwap]
  · have hne := cltSwap_cltHyb_ne d L W e hk h
    simp only [cltHyb, cltSplit, cltHybSet, cltSwap, Finset.mem_filter, Finset.mem_univ,
      true_and, Function.update_of_ne h]
    by_cases hlt : (e c : ℕ) < k
    · simp [hlt, show (e c : ℕ) < k + 1 by omega]
    · simp [hlt, show ¬ (e c : ℕ) < k + 1 by omega]

/-- The first component of the exchange, with coordinate `c` set to `0`, is `ω^{c→0}`. -/
theorem update_cltSwap_fst (c : CoordF d L W) (p : Ω d L W × Ω d L W) :
    Function.update (cltSwap d L W c p).1 c 0 = Function.update p.1 c 0 := by
  simp [cltSwap]


/-! ### The three statements -/

private theorem cltSwap_cltSplit_measurable (S : Finset (CoordF d L W)) :
    Measurable fun p : Ω d L W × Ω d L W => cltSplit d L W S p.1 p.2 := by
  refine measurable_pi_iff.2 fun c => ?_
  by_cases hc : c ∈ S
  · have h : (fun p : Ω d L W × Ω d L W => cltSplit d L W S p.1 p.2 c) = fun p => p.2 c := by
      funext p; simp [cltSplit, hc]
    rw [h]; exact (measurable_pi_apply c).comp measurable_snd
  · have h : (fun p : Ω d L W × Ω d L W => cltSplit d L W S p.1 p.2 c) = fun p => p.1 c := by
      funext p; simp [cltSplit, hc]
    rw [h]; exact (measurable_pi_apply c).comp measurable_fst

private theorem cltSwap_cltSplit_preimage_pi (S : Finset (CoordF d L W)) (s : Finset (CoordF d L W))
    (t : CoordF d L W → Set ℝ) :
    (fun p : Ω d L W × Ω d L W => cltSplit d L W S p.1 p.2) ⁻¹' ((s : Set (CoordF d L W)).pi t)
      = ((↑(s.filter fun c => c ∉ S) : Set (CoordF d L W)).pi t)
        ×ˢ ((↑(s.filter fun c => c ∈ S) : Set (CoordF d L W)).pi t) := by
  ext ⟨ω, ω'⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c hc.1
      simpa [cltSplit, hc.2] using this
    · have := h c hc.1
      simpa [cltSplit, hc.2] using this
  · rintro ⟨h1, h2⟩ c hc
    by_cases hcS : c ∈ S
    · simpa [cltSplit, hcS] using h2 c ⟨hc, hcS⟩
    · simpa [cltSplit, hcS] using h1 c ⟨hc, hcS⟩

/-- **Statement 1.**  For every set of coordinates `S`, `(ω, ω') ↦ cltSplit S ω ω'` pushes `P ⊗ P`
to `P` (the statement `MeasurePreservingCltSplit`).  Proof: test on measurable boxes
(`Measure.eq_infinitePi`); the preimage of a box is the product of the box restricted to `S` and
the box restricted to the complement of `S`.  Pattern: `measurePreserving_rowSplit`. -/
theorem measurePreserving_cltSplit : MeasurePreservingCltSplit d L W g := by
  intro S
  refine ⟨cltSwap_cltSplit_measurable d L W S, ?_⟩
  have hmeas := cltSwap_cltSplit_measurable d L W S
  change _ = Measure.infinitePi _
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    cltSwap_cltSplit_preimage_pi d L W S s t, Measure.prod_prod]
  show PF d L W g _ * PF d L W g _ = _
  rw [PF, Measure.infinitePi_pi _ fun i _ => ht i,
    Measure.infinitePi_pi _ fun i _ => ht i,
    mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not s (fun c => c ∈ S) _

private theorem cltSwap_cltSwap_involutive (c : CoordF d L W) : Function.Involutive (cltSwap d L W c) := by
  intro p
  simp [cltSwap]

/-- For every coordinate `c`, the exchange `cltSwap c` preserves `P ⊗ P` (the statement
`MeasurePreservingCltSwap`).  Proof: `P = Measure.pi μ` (finite index), so `P ⊗ P` is the image of
`Measure.pi fun c' => μ c' ⊗ μ c'` under `MeasurableEquiv.arrowProdEquivProdArrow`; there the
exchange is the coordinatewise map which is `Prod.swap` at `c` and the identity elsewhere
(`measurePreserving_pi`, `Measure.measurePreserving_swap`). -/
theorem measurePreserving_cltSwap : MeasurePreservingCltSwap d L W g := by
  intro c
  classical
  set μ : CoordF d L W → Measure ℝ := fun c' => gaussianReal 0 (gvarF d L W g c') with hμ
  have hP : PF d L W g = Measure.pi μ := Measure.infinitePi_eq_pi μ
  let A : (CoordF d L W → ℝ × ℝ) ≃ᵐ (CoordF d L W → ℝ) × (CoordF d L W → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (CoordF d L W)
  have hA : MeasurePreserving A (Measure.pi fun c' => (μ c').prod (μ c'))
      ((PF d L W g).prod (PF d L W g)) := by
    rw [hP]
    exact measurePreserving_arrowProdEquivProdArrow ℝ ℝ (CoordF d L W) μ μ
  have hG : MeasurePreserving
      (fun (a : CoordF d L W → ℝ × ℝ) (c' : CoordF d L W) =>
        (if c' = c then (Prod.swap : ℝ × ℝ → ℝ × ℝ) else id) (a c'))
      (Measure.pi fun c' => (μ c').prod (μ c')) (Measure.pi fun c' => (μ c').prod (μ c')) := by
    refine measurePreserving_pi _ _ (f := fun c' => if c' = c then Prod.swap else id) fun c' => ?_
    by_cases h : c' = c
    · simp only [h, ite_true]
      exact Measure.measurePreserving_swap
    · simp only [h, ite_false]
      exact MeasurePreserving.id _
  have hfun : cltSwap d L W c = A ∘ (fun (a : CoordF d L W → ℝ × ℝ) (c' : CoordF d L W) =>
      (if c' = c then (Prod.swap : ℝ × ℝ → ℝ × ℝ) else id) (a c')) ∘ A.symm := by
    funext p
    refine Prod.ext ?_ ?_
    · funext c'
      by_cases h : c' = c
      · subst h
        simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
      · simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          h]
    · funext c'
      by_cases h : c' = c
      · subst h
        simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
      · simp [cltSwap, A, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
          h]
  rw [hfun]
  exact (hA.comp (hG.comp (hA.symm A)))

/-- An integrand with `F ∘ cltSwap c = -F` integrates to zero against `P ⊗ P` (the
statement `IntegralEqZeroOfCltSwapNeg`).  No measurability, integrability or boundedness of `F` is used:
`cltSwap c` is a measurable involution preserving `P ⊗ P` (`measurePreserving_cltSwap`), hence
`∫ F = ∫ F ∘ cltSwap c = -∫ F`. -/
theorem integral_eq_zero_of_cltSwap_neg : IntegralEqZeroOfCltSwapNeg d L W g := by
  intro c F hF
  have hmp := measurePreserving_cltSwap d L W g c
  let σ : (Ω d L W × Ω d L W) ≃ᵐ (Ω d L W × Ω d L W) :=
    { toEquiv := (cltSwap_cltSwap_involutive d L W c).toPerm _
      measurable_toFun := hmp.measurable
      measurable_invFun := hmp.measurable }
  have hσ : MeasurePreserving σ ((PF d L W g).prod (PF d L W g)) ((PF d L W g).prod (PF d L W g)) := hmp
  have h1 : ∫ p, F (σ p) ∂((PF d L W g).prod (PF d L W g)) = ∫ p, F p ∂((PF d L W g).prod (PF d L W g)) :=
    hσ.integral_comp' F
  have h2 : ∫ p, F (σ p) ∂((PF d L W g).prod (PF d L W g)) = -∫ p, F p ∂((PF d L W g).prod (PF d L W g)) := by
    have : ∀ p, F (σ p) = -F p := fun p => hF p
    simp_rw [this]
    exact integral_neg _
  have h3 : ∫ p, F p ∂((PF d L W g).prod (PF d L W g)) = -∫ p, F p ∂((PF d L W g).prod (PF d L W g)) :=
    h1.symm.trans h2
  linear_combination (1 / 2 : ℂ) * h3

end Rep

/-- **Transfer**: an integral of a measurable function of the size-`n` slice over
`Sizes.seqP sz` is the same integral over `PF d (sz.L n) (sz.W n) (sz.lam n)`
(`Sizes.seqP_map_slice`). -/
theorem cltTransfer {d : ℕ} (sz : Sizes d) (n : ℕ) (f : Ω d (sz.L n) (sz.W n) → ℂ)
    (hf : Measurable f) :
    ∫ ω, f (Sizes.slice sz n ω) ∂(Sizes.seqP sz) =
      ∫ ω, f ω ∂(PF d (sz.L n) (sz.W n) (sz.lam n)) := by
  rw [← Sizes.seqP_map_slice sz n,
    integral_map (Sizes.measurable_slice sz n).aemeasurable hf.aestronglyMeasurable]

end RBM.Evol

end
