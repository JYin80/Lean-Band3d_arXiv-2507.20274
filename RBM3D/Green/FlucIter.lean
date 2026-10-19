/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.LDE

/-!
# Iterating the vanishing lemma: the coordinate slicing, the words in `P`, `Q`, and the pivot
expansion, `d ≥ 3`

The paper (arXiv:2507.20274) does not state these lemmas: the proof of Lemma 3.1 (`lem_GbEXP`)
says that the estimates of the lemma (among them (3.5) `GavLGEX`) have been proven as Lemma 4.1 of
[YY_25] and that their proofs are dimension-independent.  The statements are for the fine lattice
`Z_{WL}^d`.  The moment bound `integral_norm_flucAvg_pow_le_iter_budget` is in
Green/FlucIterGain.lean.

## What is proved here

Everything lives at one slice `n` of a size sequence `sz : Sizes d`, on the fine index
`Idx d (sz.L n) (sz.W n) = Z_{WL}^d`, with `E_k = condRow sz n k` (Green/FlucVanish.lean).

1. **Splitting along an arbitrary set of coordinates** (`predSplit`, `measurePreserving_predSplit`,
   `predSplit_predSplit`) and the conditional expectation `condPred` along it; `condRow` is the
   instance `p = IsRowCoord sz n k` (`condRow_eq_condPred`, `rfl`).  From it, **conditional
   expectations over different rows commute** (`condRow_condRow_comm`); no relation between the
   rows `k`, `κ` is needed.
2. **Bounded measurable functions** (`BddMeas`) and the closure lemmas.
3. **Words in `P_κ = E_κ` and `Q_κ = 1 - E_κ`** (`qRow`, `applyOps`, `numQ`), their finite
   dependence (`finDep_*`), and the exact identity `E_k (word (Q_k X)) = 0`
   (`condRow_applyOps_qRow`).
4. **The one-pivot expansion** (`pivotFam`, `prod_eq_sum_pivotFam`): writing `1 = Q_κ + P_κ` in
   every slot but the pivot, `∏_i F_i = ∑_{S ⊆ univ \ {i₀}} ∏_i pivotFam S F i`; the all-`P` term
   has integral `0` (`integral_prod_pivotFam_empty`, via `integral_mul_prod_eq_zero`).
5. **Admissible words** (`OpsOk`, `OpsOkOut`, `OpsOkOut.cons`), the word update `pivotWords`
   (`pivotFam_eq_applyOps`, `sum_numQ_pivotWords`), the crude bound `‖applyOps l X‖ ≤ 2^{numQ l} b`
   (`norm_applyOps_le`), the concrete fluctuations (`flucDiag_eq_qRow`, `bddMeas_flucDiag`) and the
   conjugation lemmas (`condRow_conj`, `qRow_conj`, `applyOps_conj`, `applyOps_epsHom`).

## Scope

The counting of multi-indices (`loneSlots`, ...) and the moment bound
`integral_norm_flucAvg_pow_le_iter_budget` are in Green/FlucIterGain.lean.  No exponent of `d`,
`W`, `L` occurs in this part, and no weight (`UniformWeight`, `BoundedWeight`).  The statements
use `condRow`, `rowSplit`, `IsRowCoord`, `RowIntegrable`, `FinDepOffRow`, `FinDep`, `epsHom`
(Green/FlucVanish.lean, Green/LDEQuad.lean); nothing of them is redefined.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Matrix Finset RBM.Gauss

section Slice1

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

/-! ### Splitting along an arbitrary set of coordinates

`rowSplit` (in Green/FlucVanish.lean) splits a sample point along the coordinates of one row.
The iteration needs several rows at once, and — more importantly — it needs to know that the
resulting conditional expectations **commute**.  Both come from one generalization: replace the
predicate `IsRowCoord sz n k` by an arbitrary decidable predicate on coordinates. -/

/-- `predSplit sz p ω ω'` takes the coordinates satisfying `p` from `ω'` and the rest from `ω`.
With `p = IsRowCoord sz n k` this is `rowSplit sz n k`. -/
def predSplit (sz : Sizes d) (p : Sizes.SeqCoord sz → Prop) [DecidablePred p]
    (ω ω' : Sizes.SeqΩ sz) : Sizes.SeqΩ sz :=
  fun c => if p c then ω' c else ω c

theorem measurable_predSplit (sz : Sizes d) (p : Sizes.SeqCoord sz → Prop) [DecidablePred p] :
    Measurable fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2 := by
  refine measurable_pi_iff.2 fun c => ?_
  by_cases hc : p c
  · have h : (fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2 c)
        = fun q => q.2 c := by
      funext q; exact ite_eq_left hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_snd
  · have h : (fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2 c)
        = fun q => q.1 c := by
      funext q; exact ite_eq_right hc
    rw [h]; exact (measurable_pi_apply c).comp measurable_fst

theorem preimage_predSplit_pi (sz : Sizes d) (p : Sizes.SeqCoord sz → Prop) [DecidablePred p]
    (s : Finset (Sizes.SeqCoord sz)) (t : Sizes.SeqCoord sz → Set ℝ) :
    (fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2) ⁻¹'
        ((s : Set (Sizes.SeqCoord sz)).pi t)
      = ((↑(s.filter fun c => ¬ p c) : Set (Sizes.SeqCoord sz)).pi t)
        ×ˢ ((↑(s.filter fun c => p c) : Set (Sizes.SeqCoord sz)).pi t) := by
  ext ⟨ω, ω'⟩
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c hc.1
      rwa [show predSplit sz p ω ω' c = ω c from ite_eq_right hc.2] at this
    · have := h c hc.1
      rwa [show predSplit sz p ω ω' c = ω' c from ite_eq_left hc.2] at this
  · rintro ⟨h1, h2⟩ c hc
    by_cases hcp : p c
    · rw [show predSplit sz p ω ω' c = ω' c from ite_eq_left hcp]; exact h2 c ⟨hc, hcp⟩
    · rw [show predSplit sz p ω ω' c = ω c from ite_eq_right hcp]; exact h1 c ⟨hc, hcp⟩

/-- **The Fubini statement behind every `E_k`.**  Taking the `p`-coordinates from one
independent copy and the rest from another reproduces the law `Sizes.seqP sz`.  This is
`measurePreserving_rowSplit` for a general predicate. -/
theorem measurePreserving_predSplit (sz : Sizes d) (p : Sizes.SeqCoord sz → Prop)
    [DecidablePred p] :
    MeasurePreserving (fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2)
      ((Sizes.seqP sz).prod (Sizes.seqP sz)) (Sizes.seqP sz) := by
  refine ⟨measurable_predSplit sz p, ?_⟩
  have hmeas := measurable_predSplit sz p
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => ht i),
    preimage_predSplit_pi sz p s t, Measure.prod_prod]
  rw [Sizes.seqP, Measure.infinitePi_pi _ fun i _ => ht i,
    Measure.infinitePi_pi _ fun i _ => ht i, mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not s p _

/-- **The composition rule for splittings.**  Splitting along `p` and then along `q` is the same
as splitting along `p ∨ q` with the two source points themselves split along `q`.  This purely
combinatorial identity is what makes the conditional expectations commute. -/
theorem predSplit_predSplit (sz : Sizes d) (p q : Sizes.SeqCoord sz → Prop) [DecidablePred p]
    [DecidablePred q] (ω ω₁ ω₂ : Sizes.SeqΩ sz) :
    predSplit sz q (predSplit sz p ω ω₁) ω₂
      = predSplit sz (fun c => p c ∨ q c) ω (predSplit sz q ω₁ ω₂) := by
  funext c
  by_cases hq : q c <;> by_cases hp : p c <;> simp [predSplit, hp, hq]

/-! ### Bounded measurable functions

Everything in this file is a bounded measurable function of `ω`: the resolvent entries are
(`measurable_green_apply`, `norm_green_apply_le_etaT`), and the class is
closed under the operations used below.  Bundling the two facts avoids carrying two hypotheses
through every lemma, and it is exactly what makes all the integrals and Fubinis unconditional. -/

/-- `X` is measurable and globally bounded. -/
structure BddMeas (sz : Sizes d) (X : Sizes.SeqΩ sz → ℂ) : Prop where
  /-- `X` is measurable. -/
  meas : Measurable X
  /-- `X` is bounded. -/
  bdd : ∃ C : ℝ, ∀ ω, ‖X ω‖ ≤ C

theorem BddMeas.integrable {X : Sizes.SeqΩ sz → ℂ} (h : BddMeas sz X) :
    Integrable X (Sizes.seqP sz) := by
  obtain ⟨C, hC⟩ := h.bdd
  exact integrable_P_of_measurable_of_bound h.meas hC

theorem BddMeas.rowIntegrable {X : Sizes.SeqΩ sz → ℂ} (h : BddMeas sz X)
    (k : Idx d (sz.L n) (sz.W n)) :
    RowIntegrable sz n k X := by
  obtain ⟨C, hC⟩ := h.bdd
  exact rowIntegrable_of_measurable_of_bound h.meas hC

theorem BddMeas.sub {X Y : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) (hY : BddMeas sz Y) :
    BddMeas sz fun ω => X ω - Y ω := by
  obtain ⟨C, hC⟩ := hX.bdd
  obtain ⟨D, hD⟩ := hY.bdd
  exact ⟨hX.meas.sub hY.meas, C + D, fun ω => le_trans (norm_sub_le _ _)
    (add_le_add (hC ω) (hD ω))⟩

theorem BddMeas.mul {X Y : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) (hY : BddMeas sz Y) :
    BddMeas sz fun ω => X ω * Y ω := by
  obtain ⟨C, hC⟩ := hX.bdd
  obtain ⟨D, hD⟩ := hY.bdd
  refine ⟨hX.meas.mul hY.meas, C * D, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC ω) (hD ω) (norm_nonneg _)
    (le_trans (norm_nonneg _) (hC (Classical.arbitrary _)))

theorem bddMeas_const (sz : Sizes d) (c : ℂ) : BddMeas sz fun _ => c :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

theorem bddMeas_prod {ι : Type*} (s : Finset ι) {f : ι → Sizes.SeqΩ sz → ℂ}
    (hf : ∀ i ∈ s, BddMeas sz (f i)) : BddMeas sz fun ω => ∏ i ∈ s, f i ω := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simpa using bddMeas_const sz 1
  | cons j t hj ih =>
      have hj' : BddMeas sz (f j) := hf j (Finset.mem_cons_self _ _)
      have ht : BddMeas sz fun ω => ∏ i ∈ t, f i ω :=
        ih fun i hi => hf i (Finset.mem_cons_of_mem hi)
      simpa only [Finset.prod_cons] using hj'.mul ht

/-! ### `E_p`, the conditional expectation along an arbitrary coordinate set -/

/-- `E_p[X](ω) = ∫ X (predSplit p ω ω') dP(ω')`.  With `p = IsRowCoord sz n k` this is
`condRow sz n k` (`condRow_eq_condPred`). -/
noncomputable def condPred (sz : Sizes d) (p : Sizes.SeqCoord sz → Prop) [DecidablePred p]
    (X : Sizes.SeqΩ sz → ℂ) :
    Sizes.SeqΩ sz → ℂ := fun ω => ∫ ω', X (predSplit sz p ω ω') ∂(Sizes.seqP sz)

theorem condRow_eq_condPred (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (X : Sizes.SeqΩ sz → ℂ) :
    condRow sz n k X = condPred sz (IsRowCoord sz n k) X := rfl

theorem condPred_congr (sz : Sizes d) {p q : Sizes.SeqCoord sz → Prop} [hp : DecidablePred p]
    [hq : DecidablePred q] (h : ∀ c, p c ↔ q c) (X : Sizes.SeqΩ sz → ℂ) :
    condPred sz p X = condPred sz q X := by
  have hpq : p = q := funext fun c => propext (h c)
  subst hpq
  exact congrArg (fun inst : DecidablePred p => @condPred d sz p inst X) (Subsingleton.elim hp hq)

theorem BddMeas.condPred {p : Sizes.SeqCoord sz → Prop} [DecidablePred p]
    {X : Sizes.SeqΩ sz → ℂ}
    (hX : BddMeas sz X) : BddMeas sz (RBM.Green.condPred sz p X) := by
  obtain ⟨C, hC⟩ := hX.bdd
  refine ⟨?_, C, fun ω => ?_⟩
  · have hjoint : StronglyMeasurable fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz =>
        X (predSplit sz p q.1 q.2) :=
      (hX.meas.comp (measurable_predSplit sz p)).stronglyMeasurable
    exact hjoint.integral_prod_right'.measurable
  · change ‖∫ ω', X (predSplit sz p ω ω') ∂(Sizes.seqP sz)‖ ≤ C
    simpa using norm_integral_le_of_norm_le_const (μ := Sizes.seqP sz)
      (f := fun ω' => X (predSplit sz p ω ω')) (C := C)
      (Filter.Eventually.of_forall fun ω' => hC _)

/-- **The double integral over an independent pair collapses.**  This is
`measurePreserving_predSplit` in integral form, and it is the only measure-theoretic
input of the iteration. -/
theorem integral_integral_predSplit (sz : Sizes d) (p : Sizes.SeqCoord sz → Prop) [DecidablePred p]
    {G : Sizes.SeqΩ sz → ℂ} (hG : BddMeas sz G) :
    ∫ ω₁, (∫ ω₂, G (predSplit sz p ω₁ ω₂) ∂(Sizes.seqP sz)) ∂(Sizes.seqP sz)
      = ∫ ν, G ν ∂(Sizes.seqP sz) := by
  have hmp := measurePreserving_predSplit sz p
  have hmap : ((Sizes.seqP sz).prod (Sizes.seqP sz)).map
      (fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2) = Sizes.seqP sz :=
    hmp.map_eq
  have hGmeas : AEStronglyMeasurable G
      (((Sizes.seqP sz).prod (Sizes.seqP sz)).map
        fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2) := by
    rw [hmap]; exact hG.meas.aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun ω₁ ω₂ => G (predSplit sz p ω₁ ω₂))
      ((Sizes.seqP sz).prod (Sizes.seqP sz)) := by
    refine (integrable_map_measure hGmeas (measurable_predSplit sz p).aemeasurable).1 ?_
    rw [hmap]; exact hG.integrable
  have hpush := integral_map (μ := (Sizes.seqP sz).prod (Sizes.seqP sz))
    (φ := fun q : Sizes.SeqΩ sz × Sizes.SeqΩ sz => predSplit sz p q.1 q.2) (f := G)
    (measurable_predSplit sz p).aemeasurable hGmeas
  rw [hmap] at hpush
  rw [integral_integral hint]
  exact hpush.symm

/-- **The conditional expectations compose.**  `E_q ∘ E_p = E_{p ∪ q}` — in particular they
**commute**, which is what lets the iteration pivot on one row after another.  The proof is the
combinatorial identity `predSplit_predSplit` followed by `integral_integral_predSplit`. -/
theorem condPred_condPred (sz : Sizes d) (p q : Sizes.SeqCoord sz → Prop) [DecidablePred p]
    [DecidablePred q]
    {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) :
    condPred sz q (condPred sz p X) = condPred sz (fun c => q c ∨ p c) X := by
  funext ω
  have hG : BddMeas sz fun ν => X (predSplit sz (fun c => q c ∨ p c) ω ν) := by
    obtain ⟨C, hC⟩ := hX.bdd
    exact ⟨hX.meas.comp ((measurable_predSplit sz fun c => q c ∨ p c).comp
      (measurable_const.prodMk measurable_id)), C, fun ν => hC _⟩
  have hkey : ∀ ω₁ ω₂ : Sizes.SeqΩ sz, X (predSplit sz p (predSplit sz q ω ω₁) ω₂)
      = (fun ν => X (predSplit sz (fun c => q c ∨ p c) ω ν)) (predSplit sz p ω₁ ω₂) := by
    intro ω₁ ω₂
    rw [predSplit_predSplit sz q p ω ω₁ ω₂]
  change (∫ ω₁, (∫ ω₂, X (predSplit sz p (predSplit sz q ω ω₁) ω₂) ∂(Sizes.seqP sz))
    ∂(Sizes.seqP sz)) = _
  simp only [hkey]
  exact integral_integral_predSplit sz p hG

/-- **`E_k` and `E_κ` commute** — a fact the iteration cannot do without.  Note that no
relation between `k` and `κ` is needed: the two rows
may share the entry `H_{kκ}`, because both sides are the single conditional expectation over the
*union* of the two rows. -/
theorem condRow_condRow_comm (sz : Sizes d) (n : ℕ) (k κ : Idx d (sz.L n) (sz.W n))
    {X : Sizes.SeqΩ sz → ℂ}
    (hX : BddMeas sz X) :
    condRow sz n k (condRow sz n κ X) = condRow sz n κ (condRow sz n k X) := by
  rw [condRow_eq_condPred, condRow_eq_condPred, condRow_eq_condPred, condRow_eq_condPred,
    condPred_condPred sz _ _ hX, condPred_condPred sz _ _ hX]
  exact condPred_congr sz (fun c => or_comm) X

/-! ### `Q_k = 1 - E_k` and words in the `P`'s and `Q`'s

A factor of the product acquires, one pivot at a time, a word of operators `P_κ = E_κ` and
`Q_κ = 1 - E_κ`.  The word is recorded as a `List (Bool × Idx d (sz.L n) (sz.W n))`, the head
being the **outermost** operator and `true` meaning `Q`. -/

/-- `Q_k X = X - E_k X`. -/
noncomputable def qRow (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (X : Sizes.SeqΩ sz → ℂ) :
    Sizes.SeqΩ sz → ℂ :=
  fun ω => X ω - condRow sz n k X ω

theorem qRow_apply (k : Idx d (sz.L n) (sz.W n)) (X : Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) :
    qRow sz n k X ω = X ω - condRow sz n k X ω := rfl

/-- `X = Q_k X + P_k X`, the splitting the expansion is built on. -/
theorem qRow_add_condRow (k : Idx d (sz.L n) (sz.W n)) (X : Sizes.SeqΩ sz → ℂ)
    (ω : Sizes.SeqΩ sz) :
    qRow sz n k X ω + condRow sz n k X ω = X ω := sub_add_cancel _ _

theorem BddMeas.condRow {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas sz (RBM.Green.condRow sz n k X) :=
  hX.condPred (p := IsRowCoord sz n k)

theorem BddMeas.qRow {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas sz (RBM.Green.qRow sz n k X) :=
  hX.sub (hX.condRow k)

@[simp] theorem condRow_zero (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) :
    condRow sz n k (0 : Sizes.SeqΩ sz → ℂ) = 0 := condRow_const k 0

/-- **`E_k ∘ Q_k = 0`** — `condRow_sub_condRow`, in the notation of this file. -/
theorem condRow_qRow {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) (k : Idx d (sz.L n) (sz.W n)) :
    condRow sz n k (qRow sz n k X) = 0 :=
  condRow_sub_condRow k (hX.rowIntegrable k)

/-- **`E_k` commutes with `Q_κ`**, for any two rows.  Together with
`condRow_condRow_comm` this says `E_k` commutes with every letter of a word. -/
theorem condRow_qRow_comm (sz : Sizes d) (n : ℕ) (k κ : Idx d (sz.L n) (sz.W n))
    {X : Sizes.SeqΩ sz → ℂ}
    (hX : BddMeas sz X) :
    condRow sz n k (qRow sz n κ X) = qRow sz n κ (condRow sz n k X) := by
  have h := condRow_sub k (hX.rowIntegrable k) ((hX.condRow κ).rowIntegrable k)
  have h2 : condRow sz n k (qRow sz n κ X)
      = fun ω => condRow sz n k X ω - condRow sz n k (condRow sz n κ X) ω := h
  rw [h2, condRow_condRow_comm sz n k κ hX]
  rfl

/-- A word in the `P`'s and `Q`'s, applied to `X`.  The head of the list is the **outermost**
operator; `true` is `Q_κ`, `false` is `P_κ`. -/
noncomputable def applyOps (sz : Sizes d) (n : ℕ) :
    List (Bool × Idx d (sz.L n) (sz.W n)) → (Sizes.SeqΩ sz → ℂ) → (Sizes.SeqΩ sz → ℂ)
  | [], X => X
  | (b, κ) :: l, X => (if b then qRow sz n κ else condRow sz n κ) (applyOps sz n l X)

@[simp] theorem applyOps_nil (sz : Sizes d) (n : ℕ) (X : Sizes.SeqΩ sz → ℂ) :
    applyOps sz n [] X = X := rfl

@[simp] theorem applyOps_cons_true (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) (X : Sizes.SeqΩ sz → ℂ) :
    applyOps sz n ((true, κ) :: l) X = qRow sz n κ (applyOps sz n l X) := rfl

@[simp] theorem applyOps_cons_false (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) (X : Sizes.SeqΩ sz → ℂ) :
    applyOps sz n ((false, κ) :: l) X = condRow sz n κ (applyOps sz n l X) := rfl

/-- The number of `Q`'s in a word: the exponent that carries the gain. -/
def numQ (l : List (Bool × Idx d (sz.L n) (sz.W n))) : ℕ := l.countP fun x => x.1

@[simp] theorem numQ_nil (sz : Sizes d) (n : ℕ) :
    numQ ([] : List (Bool × Idx d (sz.L n) (sz.W n))) = 0 := rfl

@[simp] theorem numQ_cons_true (κ : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) :
    numQ ((true, κ) :: l) = numQ l + 1 := by
  simp [numQ]

@[simp] theorem numQ_cons_false (κ : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) :
    numQ ((false, κ) :: l) = numQ l := by
  simp [numQ]

theorem BddMeas.applyOps {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X)
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) :
    BddMeas sz (RBM.Green.applyOps sz n l X) := by
  induction l with
  | nil => simpa using hX
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simpa only [applyOps_cons_false] using ih.condRow κ
      · simpa only [applyOps_cons_true] using ih.qRow κ

/-- **`E_k` commutes with any word.**  By induction on the word, from
`condRow_condRow_comm` and `condRow_qRow_comm`. -/
theorem condRow_applyOps_comm (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n)))
    {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) :
    condRow sz n k (applyOps sz n l X) = applyOps sz n l (condRow sz n k X) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simp only [applyOps_cons_false]
        rw [← ih]
        exact condRow_condRow_comm sz n k κ (hX.applyOps l)
      · simp only [applyOps_cons_true]
        rw [← ih]
        exact condRow_qRow_comm sz n k κ (hX.applyOps l)

@[simp] theorem applyOps_zero (sz : Sizes d) (n : ℕ) (l : List (Bool × Idx d (sz.L n) (sz.W n))) :
    applyOps sz n l (0 : Sizes.SeqΩ sz → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simp only [applyOps_cons_false, ih, condRow_zero]
      · simp only [applyOps_cons_true, ih]
        funext ω
        change (0 : ℂ) - condRow sz n κ (0 : Sizes.SeqΩ sz → ℂ) ω = 0
        rw [condRow_zero]; simp

/-- **The pivot factor is annihilated by `E_k`, whatever word it carries.**  This is the exact
identity the whole iteration runs on: the `Q_{k}` sitting innermost is never destroyed, because
`E_k` commutes with every letter of the word. -/
theorem condRow_applyOps_qRow (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (l : List (Bool × Idx d (sz.L n) (sz.W n)))
    {X : Sizes.SeqΩ sz → ℂ} (hX : BddMeas sz X) :
    condRow sz n k (applyOps sz n l (qRow sz n k X)) = 0 := by
  rw [condRow_applyOps_comm sz n k l (hX.qRow k), condRow_qRow hX k, applyOps_zero]

/-! ### Finite dependence of the words

`integral_mul_prod_eq_zero` needs the non-pivot factors to be `FinDepOffRow`, i.e. to
read no coordinate of the pivot row.  After a pivot they carry an outermost `P_κ`, and `E_κ` of
anything reading finitely many coordinates does not read row `κ`. -/

theorem finDep_sub {X Y : Sizes.SeqΩ sz → ℂ} (hX : FinDep sz X) (hY : FinDep sz Y) :
    FinDep sz fun ω => X ω - Y ω := by
  classical
  obtain ⟨I, hI⟩ := hX
  obtain ⟨J, hJ⟩ := hY
  refine ⟨I ∪ J, fun ω ω' hω => ?_⟩
  change X ω - Y ω = X ω' - Y ω'
  rw [hI ω ω' fun c hc => hω c (Finset.mem_union_left _ hc),
    hJ ω ω' fun c hc => hω c (Finset.mem_union_right _ hc)]

theorem finDep_condRow (k : Idx d (sz.L n) (sz.W n)) {X : Sizes.SeqΩ sz → ℂ} (h : FinDep sz X) :
    FinDep sz (condRow sz n k X) := by
  obtain ⟨I, hI⟩ := h
  refine ⟨I, fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hI _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord sz n k c
  · rw [rowSplit_apply_of_isRowCoord k ω ω'' hcr, rowSplit_apply_of_isRowCoord k ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord k ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord k ω' ω'' hcr]
    exact hω c hc

/-- **`E_κ` of a finitely-dependent function does not read row `κ`.**  This is the instance of
`FinDepOffRow` that the expansion produces at every pivot. -/
theorem finDepOffRow_condRow_self (κ : Idx d (sz.L n) (sz.W n)) {X : Sizes.SeqΩ sz → ℂ}
    (h : FinDep sz X) :
    FinDepOffRow sz n κ (condRow sz n κ X) := by
  classical
  obtain ⟨I, hI⟩ := h
  refine ⟨I.filter fun c => ¬ IsRowCoord sz n κ c, fun c hc => (Finset.mem_filter.1 hc).2,
    fun ω ω' hω => ?_⟩
  simp only [condRow_apply]
  refine congrArg _ (funext fun ω'' => hI _ _ fun c hc => ?_)
  by_cases hcr : IsRowCoord sz n κ c
  · rw [rowSplit_apply_of_isRowCoord κ ω ω'' hcr, rowSplit_apply_of_isRowCoord κ ω' ω'' hcr]
  · rw [rowSplit_apply_of_not_isRowCoord κ ω ω'' hcr,
      rowSplit_apply_of_not_isRowCoord κ ω' ω'' hcr]
    exact hω c (Finset.mem_filter.2 ⟨hc, hcr⟩)

theorem finDep_qRow (k : Idx d (sz.L n) (sz.W n)) {X : Sizes.SeqΩ sz → ℂ} (h : FinDep sz X) :
    FinDep sz (qRow sz n k X) := finDep_sub h (finDep_condRow k h)

theorem finDep_applyOps (l : List (Bool × Idx d (sz.L n) (sz.W n))) {X : Sizes.SeqΩ sz → ℂ}
    (h : FinDep sz X) :
    FinDep sz (applyOps sz n l X) := by
  induction l with
  | nil => simpa using h
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · simpa only [applyOps_cons_false] using finDep_condRow κ ih
      · simpa only [applyOps_cons_true] using finDep_qRow κ ih

/-! ### One pivot: expand, and kill the all-`P` term -/

section Pivot

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The factor family produced by one pivot on row `κ` at slot `i₀`, for the subset `S` of slots
that receive `Q_κ`; the slots outside `S` receive `P_κ`, and the pivot slot is untouched. -/
noncomputable def pivotFam (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) (i₀ : ι)
    (S : Finset ι) (F : ι → Sizes.SeqΩ sz → ℂ) (i : ι) : Sizes.SeqΩ sz → ℂ :=
  if i = i₀ then F i₀ else if i ∈ S then qRow sz n κ (F i) else condRow sz n κ (F i)

omit [Fintype ι] in
@[simp] theorem pivotFam_self (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) (i₀ : ι)
    (S : Finset ι)
    (F : ι → Sizes.SeqΩ sz → ℂ) : pivotFam sz n κ i₀ S F i₀ = F i₀ := by
  simp [pivotFam]

omit [Fintype ι] in
theorem pivotFam_of_mem (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) {i₀ : ι} {S : Finset ι}
    (F : ι → Sizes.SeqΩ sz → ℂ) {i : ι} (h : i ≠ i₀) (hi : i ∈ S) :
    pivotFam sz n κ i₀ S F i = qRow sz n κ (F i) := by
  simp [pivotFam, h, hi]

omit [Fintype ι] in
theorem pivotFam_of_not_mem (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) {i₀ : ι}
    {S : Finset ι}
    (F : ι → Sizes.SeqΩ sz → ℂ) {i : ι} (h : i ≠ i₀) (hi : i ∉ S) :
    pivotFam sz n κ i₀ S F i = condRow sz n κ (F i) := by
  simp [pivotFam, h, hi]

/-- The product of a pivoted family, split at the pivot slot. -/
theorem prod_pivotFam_eq (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) (i₀ : ι)
    {S : Finset ι}
    (hS : S ⊆ Finset.univ.erase i₀) (F : ι → Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) :
    ∏ i, pivotFam sz n κ i₀ S F i ω
      = F i₀ ω * ((∏ i ∈ S, qRow sz n κ (F i) ω)
        * ∏ i ∈ Finset.univ.erase i₀ \ S, condRow sz n κ (F i) ω) := by
  classical
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hsplit : ∏ i, pivotFam sz n κ i₀ S F i ω
      = pivotFam sz n κ i₀ S F i₀ ω * ∏ i ∈ t, pivotFam sz n κ i₀ S F i ω :=
    (Finset.mul_prod_erase Finset.univ (fun i => pivotFam sz n κ i₀ S F i ω)
      (Finset.mem_univ i₀)).symm
  have hsd : (∏ i ∈ t \ S, pivotFam sz n κ i₀ S F i ω)
      * ∏ i ∈ S, pivotFam sz n κ i₀ S F i ω = ∏ i ∈ t, pivotFam sz n κ i₀ S F i ω :=
    Finset.prod_sdiff hS
  have h1 : ∏ i ∈ S, pivotFam sz n κ i₀ S F i ω = ∏ i ∈ S, qRow sz n κ (F i) ω :=
    Finset.prod_congr rfl fun i hi => by
      rw [pivotFam_of_mem sz n κ F (Finset.mem_erase.1 (hS hi)).1 hi]
  have h2 : ∏ i ∈ t \ S, pivotFam sz n κ i₀ S F i ω
      = ∏ i ∈ t \ S, condRow sz n κ (F i) ω :=
    Finset.prod_congr rfl fun i hi => by
      obtain ⟨hit, hiS⟩ := Finset.mem_sdiff.1 hi
      rw [pivotFam_of_not_mem sz n κ F (Finset.mem_erase.1 hit).1 hiS]
  rw [hsplit, ← hsd, h1, h2, pivotFam_self]
  ring

/-- **The one-pivot expansion.**  Writing `1 = Q_κ + P_κ` in every slot but the pivot,
`∏_i F_i` becomes a sum over the subsets `S` of the non-pivot slots. -/
theorem prod_eq_sum_pivotFam (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) (i₀ : ι)
    (F : ι → Sizes.SeqΩ sz → ℂ) (ω : Sizes.SeqΩ sz) :
    ∏ i, F i ω
      = ∑ S ∈ (Finset.univ.erase i₀).powerset, ∏ i, pivotFam sz n κ i₀ S F i ω := by
  classical
  set t : Finset ι := Finset.univ.erase i₀ with ht
  have hsplit : ∏ i, F i ω = F i₀ ω * ∏ i ∈ t, F i ω :=
    (Finset.mul_prod_erase Finset.univ (fun i => F i ω) (Finset.mem_univ i₀)).symm
  have hadd : ∏ i ∈ t, F i ω
      = ∏ i ∈ t, (qRow sz n κ (F i) ω + condRow sz n κ (F i) ω) :=
    Finset.prod_congr rfl fun i _ => (qRow_add_condRow κ (F i) ω).symm
  rw [hsplit, hadd, Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [prod_pivotFam_eq sz n κ i₀ (Finset.mem_powerset.1 hS) F ω]

/-- **The all-`P` term vanishes.**  Every non-pivot factor carries an outermost `E_κ`, so it
does not read row `κ`; `E_κ` therefore passes through the product and annihilates the pivot
factor.  This is `integral_mul_prod_eq_zero`. -/
theorem integral_prod_pivotFam_empty (sz : Sizes d) (n : ℕ) {κ : Idx d (sz.L n) (sz.W n)} {i₀ : ι}
    {F : ι → Sizes.SeqΩ sz → ℂ} (hF : ∀ i, BddMeas sz (F i)) (hFd : ∀ i, FinDep sz (F i))
    (h0 : condRow sz n κ (F i₀) = 0) :
    ∫ ω, ∏ i, pivotFam sz n κ i₀ (∅ : Finset ι) F i ω ∂(Sizes.seqP sz) = 0 := by
  classical
  have hrw : ∀ ω : Sizes.SeqΩ sz, ∏ i, pivotFam sz n κ i₀ (∅ : Finset ι) F i ω
      = F i₀ ω * ∏ i ∈ Finset.univ.erase i₀, condRow sz n κ (F i) ω := by
    intro ω
    rw [prod_pivotFam_eq sz n κ i₀ (Finset.empty_subset _) F ω]
    simp
  have hint : Integrable
      (fun ω => F i₀ ω * ∏ i ∈ Finset.univ.erase i₀, condRow sz n κ (F i) ω)
      (Sizes.seqP sz) :=
    ((hF i₀).mul (bddMeas_prod _ fun i _ => (hF i).condRow κ)).integrable
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact integral_mul_prod_eq_zero (Z := F) (Y := fun i => condRow sz n κ (F i)) h0
    (fun i _ => finDepOffRow_condRow_self κ (hFd i)) hint

omit [Fintype ι] in
theorem bddMeas_pivotFam (sz : Sizes d) (n : ℕ) (κ : Idx d (sz.L n) (sz.W n)) (i₀ : ι)
    (S : Finset ι)
    {F : ι → Sizes.SeqΩ sz → ℂ} (hF : ∀ i, BddMeas sz (F i)) (i : ι) :
    BddMeas sz (pivotFam sz n κ i₀ S F i) := by
  by_cases h : i = i₀
  · subst h; rw [pivotFam_self]; exact hF i
  · by_cases hi : i ∈ S
    · rw [pivotFam_of_mem sz n κ F h hi]; exact (hF i).qRow κ
    · rw [pivotFam_of_not_mem sz n κ F h hi]; exact (hF i).condRow κ

end Pivot

/-! ### Admissible words

The gain estimate that drives the iteration — the higher-order minor expansion — needs the rows
of a word to be **pairwise distinct** and **different from the row of the slot it sits on**.
`OpsOk` is that condition; `OpsOkOut` is the strengthening carried as the induction invariant,
recording in addition that the rows already used are those of slots *outside* the set `R` of
pivots still to come. -/

section Words

variable {ι : Type*}

/-- The word `l` uses pairwise distinct rows, none of them the row `k i` of the slot it sits
on.  This is exactly the shape in which the higher-order minor expansion
`‖P_C Q_A Q_{k i} G_{k i, k i}‖ ≺ Ψ^{#A + 1}` is available. -/
def OpsOk (k : ι → Idx d (sz.L n) (sz.W n)) (i : ι) (l : List (Bool × Idx d (sz.L n) (sz.W n))) :
    Prop :=
  (l.map Prod.snd).Nodup ∧ ∀ x ∈ l, x.2 ≠ k i

variable [DecidableEq ι]

/-- `OpsOk` with the rows moreover coming from slots outside `R` — the induction invariant. -/
def OpsOkOut (k : ι → Idx d (sz.L n) (sz.W n)) (i : ι) (R : Finset ι)
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) : Prop :=
  (l.map Prod.snd).Nodup ∧ ∀ x ∈ l, (∃ j, j ∉ R ∧ x.2 = k j) ∧ x.2 ≠ k i

omit [DecidableEq ι] in
theorem opsOkOut_nil (k : ι → Idx d (sz.L n) (sz.W n)) (i : ι) (R : Finset ι) :
    OpsOkOut k i R ([] : List (Bool × Idx d (sz.L n) (sz.W n))) := ⟨by simp, by simp⟩

omit [DecidableEq ι] in
theorem OpsOkOut.opsOk {k : ι → Idx d (sz.L n) (sz.W n)} {i : ι} {R : Finset ι}
    {l : List (Bool × Idx d (sz.L n) (sz.W n))}
    (h : OpsOkOut k i R l) : OpsOk k i l := ⟨h.1, fun x hx => (h.2 x hx).2⟩

omit [DecidableEq ι] in
theorem OpsOkOut.mono {k : ι → Idx d (sz.L n) (sz.W n)} {i : ι} {R R' : Finset ι} (hR : R' ⊆ R)
    {l : List (Bool × Idx d (sz.L n) (sz.W n))} (h : OpsOkOut k i R l) : OpsOkOut k i R' l :=
  ⟨h.1, fun x hx => let ⟨⟨j, hjR, hx'⟩, hxi⟩ := h.2 x hx
    ⟨⟨j, fun hj => hjR (hR hj), hx'⟩, hxi⟩⟩

/-- **The invariant is preserved by a pivot.**  Consing the letter `(b, k i₀)` onto a word
admissible outside `R` keeps it admissible outside `R.erase i₀`, provided `i₀ ∈ R`, `i ≠ i₀`
and the row `k i₀` is **lone** — it occurs at no other slot.  Loneness is what makes the new
letter genuinely new. -/
theorem OpsOkOut.cons {k : ι → Idx d (sz.L n) (sz.W n)} {i i₀ : ι} {R : Finset ι}
    (hlone : ∀ j, j ≠ i₀ → k j ≠ k i₀) (hi₀ : i₀ ∈ R) (hne : i ≠ i₀)
    {l : List (Bool × Idx d (sz.L n) (sz.W n))} (h : OpsOkOut k i R l) (b : Bool) :
    OpsOkOut k i (R.erase i₀) ((b, k i₀) :: l) := by
  refine ⟨?_, ?_⟩
  · refine List.nodup_cons.2 ⟨fun hmem => ?_, h.1⟩
    obtain ⟨x, hx, hx'⟩ := List.mem_map.1 hmem
    obtain ⟨⟨j, hjR, hxj⟩, _⟩ := h.2 x hx
    have hj : j ≠ i₀ := fun hj => hjR (hj ▸ hi₀)
    exact hlone j hj (by rw [← hxj]; exact hx')
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨⟨i₀, Finset.notMem_erase _ _, rfl⟩, (hlone i hne).symm⟩
    · obtain ⟨⟨j, hjR, hxj⟩, hxi⟩ := h.2 x hx
      exact ⟨⟨j, fun hj => hjR (Finset.mem_of_mem_erase hj), hxj⟩, hxi⟩

end Words

/-! ### The iteration

The induction is on the number of **pivots still to be performed**.  The state is a family of
words `L i`, one per slot; the invariant is that every word is admissible outside the set `R` of
remaining pivots.  One step picks a pivot `i₀ ∈ R`, expands `1 = Q_{k i₀} + P_{k i₀}` in every
other slot, discards the all-`P` term (it vanishes) and recurses on `R.erase i₀` with the words
lengthened by one letter.  Each surviving term has at least one more `Q`, which is where the
extra factor `ρ` comes from; after `#ι` pivots the bound carries `ρ^{#ι}` on top of the trivial
`B^{#ι}`, i.e. `Ψ^{4p}` when `#ι = 2p` and `B, ρ ≍ Ψ`. -/

section Iterate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The word family after one pivot at slot `i₀`, with `Q`-set `S`. -/
def pivotWords (k : ι → Idx d (sz.L n) (sz.W n)) (i₀ : ι) (S : Finset ι)
    (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))) (i : ι) :
    List (Bool × Idx d (sz.L n) (sz.W n)) :=
  if i = i₀ then L i₀ else if i ∈ S then (true, k i₀) :: L i else (false, k i₀) :: L i

omit [Fintype ι] in
theorem pivotFam_eq_applyOps (sz : Sizes d) (n : ℕ) {k : ι → Idx d (sz.L n) (sz.W n)}
    {X : ι → Sizes.SeqΩ sz → ℂ} {i₀ : ι} {S : Finset ι}
    (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))) (i : ι) :
    pivotFam sz n (k i₀) i₀ S (fun j => applyOps sz n (L j) (qRow sz n (k j) (X j))) i
      = applyOps sz n (pivotWords k i₀ S L i) (qRow sz n (k i) (X i)) := by
  by_cases h : i = i₀
  · subst h; simp [pivotFam, pivotWords]
  · by_cases hi : i ∈ S <;> simp [pivotFam, pivotWords, h, hi]

theorem sum_numQ_pivotWords {k : ι → Idx d (sz.L n) (sz.W n)} {i₀ : ι} {S : Finset ι}
    (hS : S ⊆ Finset.univ.erase i₀) (L : ι → List (Bool × Idx d (sz.L n) (sz.W n))) :
    ∑ i, numQ (pivotWords k i₀ S L i) = (∑ i, numQ (L i)) + S.card := by
  classical
  have hi₀ : i₀ ∉ S := fun h => (Finset.mem_erase.1 (hS h)).1 rfl
  have hstep : ∀ i : ι,
      numQ (pivotWords k i₀ S L i) = numQ (L i) + (if i ∈ S then 1 else 0) := by
    intro i
    by_cases h : i = i₀
    · subst h; simp [pivotWords, hi₀]
    · by_cases hi : i ∈ S <;> simp [pivotWords, h, hi]
  simp only [hstep, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]

end Iterate

/-! ### Crude bounds

A word of `m` `Q`'s can always be bounded crudely by `2^m` times the bound on its argument
(`norm_applyOps_le`); this is what makes the gain interface `FlucGainUpTo'` of
Green/FlucIterGain.lean satisfiable at crude constants. -/

theorem norm_condRow_le {k : Idx d (sz.L n) (sz.W n)} {X : Sizes.SeqΩ sz → ℂ} {b : ℝ}
    (hX : ∀ ω, ‖X ω‖ ≤ b) (ω : Sizes.SeqΩ sz) :
    ‖condRow sz n k X ω‖ ≤ b := by
  rw [condRow_apply]
  simpa using norm_integral_le_of_norm_le_const (μ := Sizes.seqP sz)
    (f := fun ω' => X (rowSplit sz n k ω ω')) (C := b)
    (Filter.Eventually.of_forall fun ω' => hX _)

/-- The crude bound: every `Q` costs a factor `2`. -/
theorem norm_applyOps_le (l : List (Bool × Idx d (sz.L n) (sz.W n))) {X : Sizes.SeqΩ sz → ℂ}
    {b : ℝ}
    (hX : ∀ ω, ‖X ω‖ ≤ b) (ω : Sizes.SeqΩ sz) :
    ‖applyOps sz n l X ω‖ ≤ 2 ^ numQ l * b := by
  induction l generalizing ω with
  | nil => simpa using hX ω
  | cons x l ih =>
      obtain ⟨c, κ⟩ := x
      cases c
      · rw [applyOps_cons_false, numQ_cons_false]
        exact norm_condRow_le (fun ω' => ih ω') ω
      · rw [applyOps_cons_true, numQ_cons_true, pow_succ]
        have := norm_sub_condRow_le (k := κ) (X := applyOps sz n l X)
          (b := 2 ^ numQ l * b) (fun ω' => ih ω') ω
        calc ‖qRow sz n κ (applyOps sz n l X) ω‖ ≤ 2 * (2 ^ numQ l * b) := this
          _ = 2 ^ numQ l * 2 * b := by ring

/-! ### The concrete fluctuations `Z_k = (1 - E_k)(G_{kk} - m)` -/

theorem flucDiag_eq_qRow (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ) (k : Idx d (sz.L n) (sz.W n)) :
    flucDiag sz n u z m k = qRow sz n k (greenDiagCentered sz n u z m k) := rfl

theorem finDep_greenDiagCentered (sz : Sizes d) (n : ℕ) (u : ℝ) (z m : ℂ)
    (k : Idx d (sz.L n) (sz.W n)) :
    FinDep sz (greenDiagCentered sz n u z m k) :=
  finDep_of_Hflow sz n u fun H => green H z k k - m

section Env

variable {E t : ℝ}

theorem bddMeas_greenDiagCentered (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas sz (greenDiagCentered sz n u (zt E t) (mE E) k) :=
  ⟨measurable_greenDiagCentered sz n u (zt E t) (mE E) k,
    ((zt E t).im)⁻¹ + 1, norm_greenDiagCentered_le_env hE ht u k⟩

theorem bddMeas_flucDiag (hE : |E| < 2) (ht : t < 1) (u : ℝ) (k : Idx d (sz.L n) (sz.W n)) :
    BddMeas sz (flucDiag sz n u (zt E t) (mE E) k) :=
  (bddMeas_greenDiagCentered hE ht u k).qRow k

end Env

/-! ### Conjugation

Half the slots of `E|∑_k t_k Z_k|^{2p}` carry a complex conjugate.  Conjugation commutes with
every `E_k` (`integral_conj`, here in the form needed for a whole word), so a conjugated factor
is again of the form `Q_{k} X` and the iteration applies verbatim. -/

theorem condRow_conj (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) (X : Sizes.SeqΩ sz → ℂ) :
    condRow sz n k (fun ω => (starRingEnd ℂ) (X ω))
      = fun ω => (starRingEnd ℂ) (condRow sz n k X ω) := by
  funext ω
  simp only [condRow_apply]
  exact integral_conj

theorem qRow_conj (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n)) (X : Sizes.SeqΩ sz → ℂ) :
    qRow sz n k (fun ω => (starRingEnd ℂ) (X ω))
      = fun ω => (starRingEnd ℂ) (qRow sz n k X ω) := by
  funext ω
  change (starRingEnd ℂ) (X ω) - condRow sz n k (fun ω' => (starRingEnd ℂ) (X ω')) ω = _
  rw [condRow_conj]
  change _ = (starRingEnd ℂ) (X ω - condRow sz n k X ω)
  rw [map_sub]

theorem applyOps_conj (sz : Sizes d) (n : ℕ) (l : List (Bool × Idx d (sz.L n) (sz.W n)))
    (X : Sizes.SeqΩ sz → ℂ) :
    applyOps sz n l (fun ω => (starRingEnd ℂ) (X ω))
      = fun ω => (starRingEnd ℂ) (applyOps sz n l X ω) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      obtain ⟨b, κ⟩ := x
      cases b
      · rw [applyOps_cons_false, applyOps_cons_false, ih, condRow_conj]
      · rw [applyOps_cons_true, applyOps_cons_true, ih, qRow_conj]

theorem applyOps_epsHom (sz : Sizes d) (n : ℕ) (p : ℕ) (i : Fin p ⊕ Fin p)
    (l : List (Bool × Idx d (sz.L n) (sz.W n))) (X : Sizes.SeqΩ sz → ℂ) :
    applyOps sz n l (fun ω => epsHom p i (X ω))
      = fun ω => epsHom p i (applyOps sz n l X ω) := by
  cases i with
  | inl j => simp only [epsHom_inl]
  | inr j => simpa only [epsHom_inr] using applyOps_conj sz n l X

end Slice1

end RBM.Green
