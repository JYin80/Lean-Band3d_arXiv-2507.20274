/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# The generic subsequence transfer of route (A): `Sizes.comp`, `Sizes.reindex`, the exact image law

Ticket T2206 (ST-A; DECISIONS §68 (7), (8), (10): route (A), one generic ticket; supervisor
`docs/supervisor/2026-10-05-1806.md`, "Answers to REQ-2026-10-05-1746", Q1 "(A), one generic
ticket", Q2 (the regime gluing of the main induction is a later ticket), Q3 (the same gluing is
needed over the carrier and the block Anderson law)).  Paper: arXiv:2507.20274; no paper statement
and no RBM1D/RBM2D source: the stage pattern of `[s_n, t_n]` in `lem:main_ind` (`1_2:1256-1330`)
depends on `n`, so the formal proof applies the regime steps along finitely many subsequences and
glues; the paper uses this tacitly (paper-delta candidate `T2206a`).

* Section 1: `Sizes.comp φ` (the sizes along `φ`), the field lemmas, and the transfer of the
  eventual predicates (`SizeTendsto`, `Bandwidth`, `WO`, `Admissible`, `STFlow`, `STConStInd`)
  under `Tendsto φ atTop atTop`.
* Section 2: the generic exact image law of an injective coordinate reindexing of an
  `infinitePi` (every set, every integrand: product splitting `Π_ι = Π_{range f} × Π_{rest}`,
  independence of the two coordinate blocks, `Measure.prod_prod` for arbitrary sets), and its
  instances `reindex` for `seqP` and for `(sz.withLam g).seqP` (paper-delta candidate `T2206b`).
* Section 3: the commutation of the per-`n` objects with `reindex`.
* Section 4: `≺` at an arbitrary law (`map_iff`, `of_map`, `subseq`, `iff_cover`, `nth_cover`).
* Section 5: `≺` of the chain under one `comp` and the gluing composites.
* Section 6: the compiled nonempty instances at `sz0`, `φ = (2 * ·)`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

universe u v w u'

/-! ## 1. `Sizes.comp` and the transfer of the eventual and pointwise predicates -/

namespace RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **The sizes along `φ`**: the five fields of `Sizes` composed with `φ` (the sequence of sizes
`n ↦ sz n` restricted to the subsequence `j ↦ φ j`; T2206, supervisor 1806 Q1 route (A)). -/
def comp (φ : ℕ → ℕ) : Sizes d where
  L := fun j => sz.L (φ j)
  W := fun j => sz.W (φ j)
  lam := fun j => sz.lam (φ j)
  three_le_L := fun j => sz.three_le_L (φ j)
  W_pos := fun j => sz.W_pos (φ j)

/-- `N → ∞` passes to a subsequence (`Tendsto φ atTop atTop` is necessary: a constant `φ` fails). -/
theorem comp_sizeTendsto (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (h : sz.SizeTendsto) :
    (sz.comp φ).SizeTendsto := by
  unfold SizeTendsto at h ⊢
  exact h.comp hφ

/-- `(Main_DEL_COND)` (`W ≥ N^𝔠`, eventually) passes to a subsequence. -/
theorem comp_bandwidth (φ : ℕ → ℕ) (𝔠 : ℝ) (hφ : Tendsto φ atTop atTop) (h : sz.Bandwidth 𝔠) :
    (sz.comp φ).Bandwidth 𝔠 :=
  hφ.eventually h

/-- `(eq:WO)` (eventually) passes to a subsequence. -/
theorem comp_WO (φ : ℕ → ℕ) (𝔡 : ℝ) (hφ : Tendsto φ atTop atTop) (h : sz.WO 𝔡) :
    (sz.comp φ).WO 𝔡 :=
  hφ.eventually h

/-- The standing size hypotheses pass to a subsequence. -/
theorem comp_admissible (φ : ℕ → ℕ) (𝔠 𝔡 : ℝ) (hφ : Tendsto φ atTop atTop)
    (h : sz.Admissible 𝔠 𝔡) : (sz.comp φ).Admissible 𝔠 𝔡 :=
  ⟨h.1, h.2.1, comp_sizeTendsto sz φ hφ h.2.2.1, comp_bandwidth sz φ 𝔠 hφ h.2.2.2.1,
    comp_WO sz φ 𝔡 hφ h.2.2.2.2⟩

/-- The setting `STFlow` of `MR:locSC` and `zztE` restricts to a subsequence (`locDomain` pointwise). -/
theorem STFlow_comp (φ : ℕ → ℕ) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hφ : Tendsto φ atTop atTop)
    (h : STFlow sz κ ε 𝔠 𝔡 z) : STFlow (sz.comp φ) κ ε 𝔠 𝔡 (fun j => z (φ j)) :=
  ⟨comp_admissible sz φ 𝔠 𝔡 hφ h.1, fun j => h.2 (φ j)⟩

/-- `(con_st_ind)` (eventually in the size index) restricts to a subsequence. -/
theorem STConStInd_comp (φ : ℕ → ℕ) (𝔠d : ℝ) (s t : ℕ → ℝ) (hφ : Tendsto φ atTop atTop)
    (h : STConStInd sz 𝔠d s t) : STConStInd (sz.comp φ) 𝔠d (fun j => s (φ j)) (fun j => t (φ j)) :=
  hφ.eventually h

end RBM.Gauss.Sizes

/-! ## 2. The exact image law of an injective coordinate reindexing of an `infinitePi` -/

namespace RBM.Gauss

section InfinitePiComp

variable {ι : Type u} {α : Type v} {X : ι → Type w} [∀ i, MeasurableSpace (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)] (f : α → ι)

/-- The measurable equivalence `Π_ι X ≃ᵐ Π_α X(f ·) × Π_{ι ∖ range f} X` (the product splitting). -/
private noncomputable def sizesComp_split (hf : Function.Injective f) :
    (∀ i, X i) ≃ᵐ (∀ a, X (f a)) × (∀ k : {i // ¬ i ∈ Set.range f}, X k.1) := by
  classical
  exact (MeasurableEquiv.piEquivPiSubtypeProd X (fun i => i ∈ Set.range f)).trans
    ((MeasurableEquiv.piCongrLeft (fun i : Set.range f => X i.1)
      (Equiv.ofInjective f hf)).symm.prodCongr (MeasurableEquiv.refl _))

private theorem sizesComp_split_apply (hf : Function.Injective f) (ω : ∀ i, X i) :
    sizesComp_split f hf ω = ((fun a => ω (f a)), (fun k : {i // ¬ i ∈ Set.range f} => ω k.1)) := by
  classical
  refine Prod.ext ?_ ?_
  · funext a
    rfl
  · funext k
    rfl

/-- The two blocks of coordinates, `range f` and its complement, are independent under `infinitePi`. -/
private theorem sizesComp_indepFun_split :
    IndepFun (fun (ω : ∀ i, X i) (a : α) => ω (f a))
      (fun (ω : ∀ i, X i) (k : {i // ¬ i ∈ Set.range f}) => ω k.1) (Measure.infinitePi μ) := by
  have h := iIndepFun_infinitePi (P := μ) (X := fun i (x : X i) => x) (fun i => measurable_id)
  have hi := indep_iSup_of_disjoint (fun i => (measurable_pi_apply (X := X) i).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 h) (S := Set.range f) (T := (Set.range f)ᶜ)
    disjoint_compl_right
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hi ?_) ?_
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun k => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun i (_ : i ∈ (Set.range f)ᶜ) =>
      MeasurableSpace.comap (fun ω : ∀ i, X i => ω i) inferInstance) k.1 k.2
  · rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun a => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun i (_ : i ∈ Set.range f) =>
      MeasurableSpace.comap (fun ω : ∀ i, X i => ω i) inferInstance) (f a) ⟨a, rfl⟩

/-- The joint law of the two blocks is the product of the two marginals. -/
private theorem sizesComp_map_split (hf : Function.Injective f) :
    (Measure.infinitePi μ).map (sizesComp_split f hf) =
      (Measure.infinitePi fun a => μ (f a)).prod
        (Measure.infinitePi fun k : {i // ¬ i ∈ Set.range f} => μ k.1) := by
  have h1 := (sizesComp_indepFun_split μ f).map_prod_eq_prod_map_map
    (by fun_prop : Measurable (fun (ω : ∀ i, X i) (a : α) => ω (f a))).aemeasurable
    (by fun_prop : Measurable
      (fun (ω : ∀ i, X i) (k : {i // ¬ i ∈ Set.range f}) => ω k.1)).aemeasurable
  have h2 : (sizesComp_split f hf : (∀ i, X i) → _) = fun ω =>
      ((fun a => ω (f a)), (fun k : {i // ¬ i ∈ Set.range f} => ω k.1)) :=
    funext (sizesComp_split_apply f hf)
  rw [h2, h1, Measure.map_infinitePi_infinitePi_of_inj hf]
  congr 1
  exact Measure.infinitePi_map_restrict' (μ := μ) (I := (Set.range f)ᶜ)

/-- **The exact image law** of an injective reindexing of an `infinitePi`, on **every** set (measurable
or not): `infinitePi μ ((ω ↦ ω ∘ f) ⁻¹' s) = infinitePi (μ ∘ f) s`.  The bad sets of `StochDomAt`
are unions over uncountable parameter sets, so `MeasurePreserving` (which gives `≤` only) does not
suffice for the direction `sz → sz.comp φ`.  Proof: `Π_ι ≃ᵐ Π_α × Π_rest`, independence of the
blocks, `MeasurableEquiv.map_apply` and `Measure.prod_prod` (no measurability of the set). -/
theorem infinitePi_preimage_comp (hf : Function.Injective f) (s : Set (∀ a, X (f a))) :
    Measure.infinitePi μ ((fun (ω : ∀ i, X i) (a : α) => ω (f a)) ⁻¹' s) =
      Measure.infinitePi (fun a => μ (f a)) s := by
  have h1 : (fun (ω : ∀ i, X i) (a : α) => ω (f a)) ⁻¹' s =
      sizesComp_split f hf ⁻¹' (s ×ˢ (Set.univ : Set (∀ k : {i // ¬ i ∈ Set.range f}, X k.1))) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, sizesComp_split_apply]
  rw [h1, ← MeasurableEquiv.map_apply, sizesComp_map_split μ f hf, Measure.prod_prod, measure_univ,
    mul_one]

/-- The exact image law for integrals: every integrand (no measurability), any real normed space. -/
theorem integral_infinitePi_comp (hf : Function.Injective f)
    {E : Type u'} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : (∀ a, X (f a)) → E) :
    ∫ ω : (∀ i, X i), g (fun a => ω (f a)) ∂(Measure.infinitePi μ) =
      ∫ y, g y ∂(Measure.infinitePi fun a => μ (f a)) := by
  have h1 : (fun ω : (∀ i, X i) => g (fun a => ω (f a))) =
      fun ω => (fun p : (∀ a, X (f a)) × (∀ k : {i // ¬ i ∈ Set.range f}, X k.1) => g p.1)
        (sizesComp_split f hf ω) := by
    funext ω
    rw [sizesComp_split_apply]
  rw [h1, ← integral_map_equiv (sizesComp_split f hf)
    (fun p : (∀ a, X (f a)) × (∀ k : {i // ¬ i ∈ Set.range f}, X k.1) => g p.1),
    sizesComp_map_split μ f hf, integral_fun_fst]
  simp

end InfinitePiComp

end RBM.Gauss

namespace RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

/-- The index map of the reindexing: `⟨j, c⟩ ↦ ⟨φ j, c⟩`. -/
def reindexCoord (φ : ℕ → ℕ) : SeqCoord (sz.comp φ) → SeqCoord sz :=
  fun p => ⟨φ p.1, p.2⟩

theorem reindexCoord_injective (φ : ℕ → ℕ) (hφ : Function.Injective φ) :
    Function.Injective (reindexCoord sz φ) := by
  rintro ⟨j, c⟩ ⟨j', c'⟩ h
  have hj : φ j = φ j' := congrArg Sigma.fst h
  obtain rfl := hφ hj
  exact congrArg (Sigma.mk j) (eq_of_heq (Sigma.mk.inj h).2)

/-- **The reindexing** of the common sample space: `ω ↦ (⟨j, c⟩ ↦ ω ⟨φ j, c⟩)`. -/
def reindex (φ : ℕ → ℕ) (ω : SeqΩ sz) : SeqΩ (sz.comp φ) :=
  fun p => ω ⟨φ p.1, p.2⟩

theorem measurable_reindex (φ : ℕ → ℕ) : Measurable (reindex sz φ) :=
  measurable_pi_iff.2 fun p => measurable_pi_apply (⟨φ p.1, p.2⟩ : SeqCoord sz)

/-- The exact image law of `seqP` under the reindexing of an injective `φ`, on every set. -/
theorem seqP_reindex_preimage (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (s : Set (SeqΩ (sz.comp φ))) : seqP sz (reindex sz φ ⁻¹' s) = seqP (sz.comp φ) s :=
  Gauss.infinitePi_preimage_comp (fun c : SeqCoord sz => gaussianReal 0 (seqGvar sz c))
    (reindexCoord sz φ) (reindexCoord_injective sz φ hφ) s

/-- The same for the block Anderson law `(sz.withLam g).seqP`, on the common space `SeqΩ sz`
(which does not see `lam`): the law of `sz.withLam g` pulled back along `reindex sz φ` is the law
of `(sz.comp φ).withLam (g ∘ φ)`. -/
theorem seqP_withLam_reindex_preimage (φ : ℕ → ℕ) (g : ℕ → ℝ) (hφ : Function.Injective φ)
    (s : Set (SeqΩ ((sz.comp φ).withLam fun j => g (φ j)))) :
    seqP (sz.withLam g) (reindex sz φ ⁻¹' s) = seqP ((sz.comp φ).withLam fun j => g (φ j)) s :=
  seqP_reindex_preimage (sz.withLam g) φ hφ s

/-- `reindex` is measure preserving (`seqP sz → seqP (sz.comp φ)`), `φ` injective. -/
theorem measurePreserving_reindex (φ : ℕ → ℕ) (hφ : Function.Injective φ) :
    MeasurePreserving (reindex sz φ) (seqP sz) (seqP (sz.comp φ)) := by
  refine ⟨measurable_reindex sz φ, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_reindex sz φ) hs]
  exact seqP_reindex_preimage sz φ hφ s

/-- The exact image law for integrals: every integrand, any real normed space. -/
theorem integral_reindex (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : SeqΩ (sz.comp φ) → E) :
    ∫ ω, g (reindex sz φ ω) ∂(seqP sz) = ∫ ω, g ω ∂(seqP (sz.comp φ)) :=
  Gauss.integral_infinitePi_comp (fun c : SeqCoord sz => gaussianReal 0 (seqGvar sz c))
    (reindexCoord sz φ) (reindexCoord_injective sz φ hφ) g

end RBM.Gauss.Sizes

/-! ## 3. The per-`n` objects commute with the reindexing

Each object below depends on `sz` only through `sz.L n`, `sz.W n`, `sz.lam n` and on `ω` only through
`slice sz n ω`; at the subsequence index `j` these are `sz.L (φ j)` etc., and `slice (sz.comp φ) j
(reindex sz φ ω) = slice sz (φ j) ω`.  So the statements are `rfl`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

theorem Lloop_reindex (φ : ℕ → ℕ) (j : ℕ) (E t : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → RBM.Zd d (sz.L (φ j))) (ω : SeqΩ sz) :
    Lloop (sz.comp φ) j E t σ a (reindex sz φ ω) = Lloop sz (φ j) E t σ a ω := rfl

/-- The deterministic left side of `STExp2` (`Induction/Defs.lean:159`) integrates over the whole
law `seqP`, not over the coordinate `n`: it transfers by the exact image law of `integral_reindex`. -/
theorem integral_Lloop_reindex (φ : ℕ → ℕ) (hφ : Function.Injective φ) (j : ℕ) (E t : ℝ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → RBM.Zd d (sz.L (φ j))) :
    ∫ ω, Lloop (sz.comp φ) j E t σ a ω ∂(seqP (sz.comp φ)) =
      ∫ ω, Lloop sz (φ j) E t σ a ω ∂(seqP sz) := by
  rw [← integral_reindex sz φ hφ (fun ω => Lloop (sz.comp φ) j E t σ a ω)]
  exact integral_congr_ae (Eventually.of_forall fun ω => Lloop_reindex sz φ j E t σ a ω)

end RBM.Gauss.Sizes

/-! ## 4. `≺` at an arbitrary law: image laws, subsequences, finite covers

The three predicates are `∀ τ D, ∀ᶠ l, <bound at l>`.  A map `f : Ω₀ → Ω₁` with `μ (f ⁻¹' s) = ν s`
for **every** set `s` (not only measurable ones) carries them in both directions
(`map_iff`); along a subsequence `φ` with `Tendsto φ atTop atTop` they restrict (`subseq`); a finite
family of strictly increasing `φ k` whose ranges cover all large `n` recovers them (`iff_cover`);
a finite partition of `ℕ` is covered by the `Nat.nth` enumerations of its infinite classes
(`nth_cover`). -/

namespace RBM

/-- A finite family of strictly increasing enumerations whose ranges contain all large `n` glues an
eventual statement: if `P` holds eventually along each `φ k`, it holds eventually. -/
private theorem sizesComp_eventually_of_cover {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k))
    {P : ℕ → Prop} (h : ∀ k, ∀ᶠ j in atTop, P (φ k j)) : ∀ᶠ n in atTop, P n := by
  have h1 : ∀ k, ∀ᶠ n in atTop, ∀ j, φ k j = n → P n := by
    intro k
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (h k)
    refine eventually_atTop.2 ⟨φ k J, fun n hn j hj => ?_⟩
    have hjJ : J ≤ j := (hφ k).le_iff_le.1 (hj ▸ hn)
    exact hj ▸ hJ j hjJ
  filter_upwards [hcov, eventually_all.2 h1] with n ⟨k, j, hj⟩ hall
  exact hall k j hj

namespace StochDomAt

/-- **Exact image law for `≺`**: if `μ (f ⁻¹' s) = ν s` for every set `s` of `Ω₁`, then `≺` under `ν`
is `≺` of the pulled-back families under `μ` (the bad set of the pulled-back family is the
preimage of the bad set, `rfl`).  T2206 target 5. -/
theorem map_iff {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    (μ : Measure Ω₀) (ν : Measure Ω₁) (f : Ω₀ → Ω₁) (hf : ∀ s : Set Ω₁, μ (f ⁻¹' s) = ν s)
    (size : ℕ → ℕ) {U : ℕ → Type w} (ξ ζ : ∀ l, U l → Ω₁ → ℝ) :
    RBM.StochDomAt ν size ξ ζ ↔
      RBM.StochDomAt μ size (U := U) (fun l u ω => ξ l u (f ω)) (fun l u ω => ζ l u (f ω)) := by
  unfold RBM.StochDomAt
  refine forall₂_congr fun τ _ => forall₂_congr fun D _ => eventually_congr (Eventually.of_forall
    fun l => ?_)
  rw [show badSetAt size (fun l u ω => ξ l u (f ω)) (fun l u ω => ζ l u (f ω)) τ l =
    f ⁻¹' badSetAt size ξ ζ τ l from rfl, hf]

/-- `≺` along `size` restricts to `≺` along `size ∘ φ`, for `φ` tending to infinity. -/
theorem subseq {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ)
    {U : ℕ → Type v} (ξ ζ : ∀ l, U l → Ω₀ → ℝ) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (h : RBM.StochDomAt μ size ξ ζ) :
    RBM.StochDomAt μ (fun j => size (φ j)) (U := fun j => U (φ j)) (fun j => ξ (φ j))
      (fun j => ζ (φ j)) := fun τ hτ D hD => hφ.eventually (h τ hτ D hD)

/-- **The cover lemma**: finitely many strictly increasing `φ k` whose ranges contain all large `n`:
`≺` along `size` is equivalent to `≺` along every `size ∘ φ k`.  (`StrictMono` is used in
`n = φ k j ≥ φ k J ⇒ j ≥ J`; `ι` is finite and the cover is eventual, so the finitely many
thresholds have a maximum.) -/
theorem iff_cover {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ)
    {U : ℕ → Type v} (ξ ζ : ∀ l, U l → Ω₀ → ℝ) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    RBM.StochDomAt μ size ξ ζ ↔
      ∀ k, RBM.StochDomAt μ (fun j => size (φ k j)) (U := fun j => U (φ k j))
        (fun j => ξ (φ k j)) (fun j => ζ (φ k j)) := by
  refine ⟨fun h k => subseq μ size ξ ζ (φ k) (hφ k).tendsto_atTop h, fun h τ hτ D hD => ?_⟩
  exact sizesComp_eventually_of_cover φ hφ hcov fun k => h k τ hτ D hD

end StochDomAt

end RBM

namespace RBM

/-- **A finite partition of `ℕ` is covered by the `Nat.nth` enumerations of its infinite classes**
(the finite classes are bounded, so they do not matter for eventual statements).  Each enumeration
is strictly increasing (`Nat.nth_strictMono`), its range is the class (`Nat.range_nth_of_infinite`). -/
theorem nth_cover {ι : Type w} [Finite ι] (c : ℕ → ι) :
    ∀ᶠ n in atTop, ∃ i : {i : ι // {m : ℕ | c m = i}.Infinite},
      n ∈ Set.range (Nat.nth (fun m => c m = i.1)) := by
  have h : ∀ i : ι, ∀ᶠ n in atTop, {m : ℕ | c m = i}.Finite → n ∉ {m : ℕ | c m = i} := by
    intro i
    by_cases hi : {m : ℕ | c m = i}.Finite
    · rw [← Nat.cofinite_eq_atTop]
      filter_upwards [hi.eventually_cofinite_notMem] with n hn _ using hn
    · exact Eventually.of_forall fun n h' => (hi h').elim
  filter_upwards [eventually_all.2 h] with n hn
  have hinf : {m : ℕ | c m = c n}.Infinite := fun hfin => hn (c n) hfin rfl
  exact ⟨⟨c n, hinf⟩, by rw [Nat.range_nth_of_infinite hinf]; rfl⟩

end RBM

/-! ## 5. `≺` of the chain under `Sizes.comp`, and the gluing composites -/

namespace RBM.Gauss.Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **Exact pullback** (`φ` injective): `≺` on the subsequence sizes under `seqP (sz.comp φ)` is `≺`
on the original law `seqP sz` along `φ`, for the pulled-back families
(`(sz.comp φ).size = sz.size ∘ φ` is `rfl`; the law is `seqP_reindex_preimage`). -/
theorem Prec_comp_iff (φ : ℕ → ℕ) (hφ : Function.Injective φ) {U : ℕ → Type u}
    (ξ ζ : ∀ j, U j → SeqΩ (sz.comp φ) → ℝ) :
    Prec (sz.comp φ) ξ ζ ↔
      RBM.StochDomAt (seqP sz) (fun j => sz.size (φ j)) (U := U)
        (fun j u ω => ξ j u (reindex sz φ ω)) (fun j u ω => ζ j u (reindex sz φ ω)) :=
  RBM.StochDomAt.map_iff (seqP sz) (seqP (sz.comp φ)) (reindex sz φ)
    (seqP_reindex_preimage sz φ hφ) (fun j => sz.size (φ j)) ξ ζ

/-- Forward along one subsequence, for families `ξ' ζ'` on `sz.comp φ` that commute with the
`sz`-families at `φ j`. -/
theorem Prec_comp (φ : ℕ → ℕ) (hφ : StrictMono φ) {U : ℕ → Type u}
    (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) (ξ' ζ' : ∀ j, U (φ j) → SeqΩ (sz.comp φ) → ℝ)
    (hξ : ∀ j u ω, ξ' j u (reindex sz φ ω) = ξ (φ j) u ω)
    (hζ : ∀ j u ω, ζ' j u (reindex sz φ ω) = ζ (φ j) u ω)
    (h : Prec sz ξ ζ) : Prec (sz.comp φ) (U := fun j => U (φ j)) ξ' ζ' := by
  have h1 := RBM.StochDomAt.subseq (seqP sz) sz.size ξ ζ φ hφ.tendsto_atTop h
  rw [Prec_comp_iff sz φ hφ.injective]
  have e1 : (fun j u ω => ξ' j u (reindex sz φ ω)) = fun j => ξ (φ j) := by
    funext j u ω; exact hξ j u ω
  have e2 : (fun j u ω => ζ' j u (reindex sz φ ω)) = fun j => ζ (φ j) := by
    funext j u ω; exact hζ j u ω
  rw [e1, e2]
  exact h1

/-- **Law-generic gluing** (the `PrecL` form of the held T2197, `StochDomAt μ sz.size`, stated without
that name): a law `μ` on `SeqΩ sz`, laws `ν k` on `SeqΩ (sz.comp (φ k))` with
`μ (reindex sz (φ k) ⁻¹' s) = ν k s` for every set `s`, a finite `StrictMono` cover and commuting
families: `≺` under `μ` along `sz.size` iff `≺` under every `ν k` along `(sz.comp (φ k)).size`. -/
theorem stochDomAt_iff_comp_cover (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι]
    (φ : ι → ℕ → ℕ) (ν : ∀ k, Measure (SeqΩ (sz.comp (φ k)))) (hφ : ∀ k, StrictMono (φ k))
    (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k))
    (hlaw : ∀ k (s : Set (SeqΩ (sz.comp (φ k)))), μ (reindex sz (φ k) ⁻¹' s) = ν k s)
    {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ)
    (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (sz.comp (φ k)) → ℝ)
    (hξ : ∀ k j u ω, ξ' k j u (reindex sz (φ k) ω) = ξ (φ k j) u ω)
    (hζ : ∀ k j u ω, ζ' k j u (reindex sz (φ k) ω) = ζ (φ k j) u ω) :
    RBM.StochDomAt μ sz.size ξ ζ ↔
      ∀ k, RBM.StochDomAt (ν k) (sz.comp (φ k)).size (U := fun j => U (φ k j)) (ξ' k) (ζ' k) := by
  refine (RBM.StochDomAt.iff_cover μ sz.size ξ ζ φ hφ hcov).trans (forall_congr' fun k => ?_)
  have e1 : (fun j u ω => ξ' k j u (reindex sz (φ k) ω)) = fun j => ξ (φ k j) := by
    funext j u ω; exact hξ k j u ω
  have e2 : (fun j u ω => ζ' k j u (reindex sz (φ k) ω)) = fun j => ζ (φ k j) := by
    funext j u ω; exact hζ k j u ω
  have := RBM.StochDomAt.map_iff μ (ν k) (reindex sz (φ k)) (hlaw k) (sz.comp (φ k)).size
    (U := fun j => U (φ k j)) (ξ' k) (ζ' k)
  rw [e1, e2] at this
  exact this.symm

/-- **The model law**: what the main-induction regime gluing uses (premises `sz → sz.comp (φ k)`,
conclusions back). -/
theorem Prec_iff_comp_cover {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k))
    (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) {U : ℕ → Type u}
    (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (sz.comp (φ k)) → ℝ)
    (hξ : ∀ k j u ω, ξ' k j u (reindex sz (φ k) ω) = ξ (φ k j) u ω)
    (hζ : ∀ k j u ω, ζ' k j u (reindex sz (φ k) ω) = ζ (φ k j) u ω) :
    Prec sz ξ ζ ↔ ∀ k, Prec (sz.comp (φ k)) (U := fun j => U (φ k j)) (ξ' k) (ζ' k) :=
  stochDomAt_iff_comp_cover sz (seqP sz) φ (fun k => seqP (sz.comp (φ k))) hφ hcov
    (fun k s => seqP_reindex_preimage sz (φ k) (hφ k).injective s) ξ ζ ξ' ζ' hξ hζ

end RBM.Gauss.Sizes

/-! ## 6. The compiled nonempty instances: `d = 3`, `sz0`, `φ = (2 * ·)`

`sz0` (`Defs/Sizes.lean:260`) has `L n = 4 (n+1)`, `W n = (2 (n+1))^5`, `lam n = (2 (n+1))^{-6}`; the
subsequence `φ j = 2 j` is `StrictMono`, injective and tends to infinity.  Every deterministic
hypothesis is discharged; what stays a hypothesis of an instance is a stochastic premise of
`STLK`, `STExp2` (a `Prec` statement). -/

/-! ### Extra instances: the deterministic family `ξ = 0 ≺ ζ = 1`, so that every generic target is applied
at concrete data with nothing left open (the premises of instances 7-9 are stochastic and stay
hypotheses). -/
