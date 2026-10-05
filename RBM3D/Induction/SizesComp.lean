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

@[simp] theorem comp_L (φ : ℕ → ℕ) (j : ℕ) : (sz.comp φ).L j = sz.L (φ j) := rfl

@[simp] theorem comp_W (φ : ℕ → ℕ) (j : ℕ) : (sz.comp φ).W j = sz.W (φ j) := rfl

@[simp] theorem comp_lam (φ : ℕ → ℕ) (j : ℕ) : (sz.comp φ).lam j = sz.lam (φ j) := rfl

@[simp] theorem comp_size (φ : ℕ → ℕ) (j : ℕ) : (sz.comp φ).size j = sz.size (φ j) := rfl

@[simp] theorem withLam_comp (g : ℕ → ℝ) (φ : ℕ → ℕ) :
    (sz.withLam g).comp φ = (sz.comp φ).withLam (fun j => g (φ j)) := rfl

@[simp] theorem comp_locDomain (φ : ℕ → ℕ) (κ ε : ℝ) (j : ℕ) (z : ℂ) :
    (sz.comp φ).locDomain κ ε j z ↔ sz.locDomain κ ε (φ j) z := Iff.rfl

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

theorem reindex_eq (φ : ℕ → ℕ) (ω : SeqΩ sz) : reindex sz φ ω = ω ∘ reindexCoord sz φ := rfl

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

theorem slice_reindex (φ : ℕ → ℕ) (j : ℕ) (ω : SeqΩ sz) :
    slice (sz.comp φ) j (reindex sz φ ω) = slice sz (φ j) ω := rfl

theorem seqXmat_reindex (φ : ℕ → ℕ) (j : ℕ) (ω : SeqΩ sz) :
    seqXmat (sz.comp φ) j (reindex sz φ ω) = seqXmat sz (φ j) ω := rfl

theorem seqHflow_reindex (φ : ℕ → ℕ) (j : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    seqHflow (sz.comp φ) j u (reindex sz φ ω) = seqHflow sz (φ j) u ω := rfl

theorem Gt_reindex (φ : ℕ → ℕ) (j : ℕ) (E t : ℝ) (σ : Bool) (ω : SeqΩ sz) :
    Gt (sz.comp φ) j E t σ (reindex sz φ ω) = Gt sz (φ j) E t σ ω := rfl

theorem Lloop_reindex (φ : ℕ → ℕ) (j : ℕ) (E t : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → RBM.Zd d (sz.L (φ j))) (ω : SeqΩ sz) :
    Lloop (sz.comp φ) j E t σ a (reindex sz φ ω) = Lloop sz (φ j) E t σ a ω := rfl

theorem STGM_reindex (φ : ℕ → ℕ) (j : ℕ) (E τ : ℝ) (ω : SeqΩ sz)
    (x y : RBM.Gauss.Idx d (sz.L (φ j)) (sz.W (φ j))) :
    STGM (sz.comp φ) j E τ (reindex sz φ ω) x y = STGM sz (φ j) E τ ω x y := rfl

theorem STKloop_comp (φ : ℕ → ℕ) (j : ℕ) (E τ : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → RBM.Zd d (sz.L (φ j))) :
    STKloop (sz.comp φ) j E τ σ a = STKloop sz (φ j) E τ σ a := rfl

theorem Bctl_comp (φ : ℕ → ℕ) (j : ℕ) (t : ℝ) : (sz.comp φ).Bctl j t = sz.Bctl (φ j) t := rfl

theorem STWB_comp (φ : ℕ → ℕ) (j : ℕ) (τ : ℝ) (K : ℕ) :
    STWB (sz.comp φ) j τ K = STWB sz (φ j) τ K := rfl

theorem STblk_comp (φ : ℕ → ℕ) (j : ℕ) (x : RBM.Gauss.Idx d (sz.L (φ j)) (sz.W (φ j))) :
    STblk (sz.comp φ) j x = STblk sz (φ j) x := rfl

theorem ellT_comp (φ : ℕ → ℕ) (j : ℕ) (τ : ℝ) :
    RBM.ellT ((sz.comp φ).L j) ((sz.comp φ).lam j) τ = RBM.ellT (sz.L (φ j)) (sz.lam (φ j)) τ :=
  rfl

theorem STflowE_comp (z : ℕ → ℂ) (φ : ℕ → ℕ) :
    STflowE (fun j => z (φ j)) = fun j => STflowE z (φ j) := rfl

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

/-- The cheap direction: a measurable `f` with `μ.map f = ν` carries `≺` forward
(`Measure.le_map_apply`: `μ (f ⁻¹' s) ≤ (μ.map f) s` for every `s`); for a merely measure
preserving `f` this is all one gets, which is the direction `sz.comp φ → sz` of the gluing. -/
theorem of_map {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    (μ : Measure Ω₀) (ν : Measure Ω₁) (f : Ω₀ → Ω₁) (hf : Measurable f) (hμν : μ.map f = ν)
    (size : ℕ → ℕ) {U : ℕ → Type w} (ξ ζ : ∀ l, U l → Ω₁ → ℝ)
    (h : RBM.StochDomAt ν size ξ ζ) :
    RBM.StochDomAt μ size (U := U) (fun l u ω => ξ l u (f ω)) (fun l u ω => ζ l u (f ω)) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl
  refine le_trans ?_ hl
  rw [← hμν]
  exact Measure.le_map_apply hf.aemeasurable (badSetAt size ξ ζ τ l)

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

namespace RBM.Path.PerTimeDomAt

/-- Exact image law for per-time `≺` (see `RBM.StochDomAt.map_iff`). -/
theorem map_iff {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    (μ : Measure Ω₀) (ν : Measure Ω₁) (f : Ω₀ → Ω₁) (hf : ∀ s : Set Ω₁, μ (f ⁻¹' s) = ν s)
    (size : ℕ → ℕ) {U : ℕ → Type w} (ξ ζ : ∀ l, U l → Ω₁ → ℝ) :
    RBM.Path.PerTimeDomAt ν size ξ ζ ↔
      RBM.Path.PerTimeDomAt μ size (U := U) (fun l u ω => ξ l u (f ω)) (fun l u ω => ζ l u (f ω)) := by
  unfold RBM.Path.PerTimeDomAt
  refine forall₂_congr fun τ _ => forall₂_congr fun D _ => eventually_congr (Eventually.of_forall
    fun l => forall_congr' fun u => ?_)
  rw [show {ω | (size l : ℝ) ^ τ * ζ l u (f ω) < ξ l u (f ω)} =
    f ⁻¹' {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} from rfl, hf]

/-- Per-time `≺` along `size` restricts to `size ∘ φ`, for `φ` tending to infinity. -/
theorem subseq {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ)
    {U : ℕ → Type v} (ξ ζ : ∀ l, U l → Ω₀ → ℝ) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (h : RBM.Path.PerTimeDomAt μ size ξ ζ) :
    RBM.Path.PerTimeDomAt μ (fun j => size (φ j)) (U := fun j => U (φ j)) (fun j => ξ (φ j))
      (fun j => ζ (φ j)) := fun τ hτ D hD => hφ.eventually (h τ hτ D hD)

/-- The cover lemma for per-time `≺` (see `RBM.StochDomAt.iff_cover`). -/
theorem iff_cover {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ)
    {U : ℕ → Type v} (ξ ζ : ∀ l, U l → Ω₀ → ℝ) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    RBM.Path.PerTimeDomAt μ size ξ ζ ↔
      ∀ k, RBM.Path.PerTimeDomAt μ (fun j => size (φ k j)) (U := fun j => U (φ k j))
        (fun j => ξ (φ k j)) (fun j => ζ (φ k j)) := by
  refine ⟨fun h k => subseq μ size ξ ζ (φ k) (hφ k).tendsto_atTop h, fun h τ hτ D hD => ?_⟩
  exact RBM.sizesComp_eventually_of_cover φ hφ hcov fun k => h k τ hτ D hD

end RBM.Path.PerTimeDomAt

namespace RBM.Gauss.HighProbAt

/-- Exact image law for `w.h.p.` (see `RBM.StochDomAt.map_iff`): the complement of a preimage is the
preimage of the complement. -/
theorem map_iff {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁]
    (μ : Measure Ω₀) (ν : Measure Ω₁) (f : Ω₀ → Ω₁) (hf : ∀ s : Set Ω₁, μ (f ⁻¹' s) = ν s)
    (size : ℕ → ℕ) (Ξ : ℕ → Set Ω₁) :
    RBM.Gauss.HighProbAt ν size Ξ ↔ RBM.Gauss.HighProbAt μ size (fun l => f ⁻¹' Ξ l) := by
  unfold RBM.Gauss.HighProbAt
  refine forall₂_congr fun D _ => eventually_congr (Eventually.of_forall fun l => ?_)
  rw [← Set.preimage_compl, hf]

/-- `w.h.p.` along `size` restricts to `size ∘ φ`, for `φ` tending to infinity. -/
theorem subseq {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ)
    (Ξ : ℕ → Set Ω₀) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (h : RBM.Gauss.HighProbAt μ size Ξ) :
    RBM.Gauss.HighProbAt μ (fun j => size (φ j)) (fun j => Ξ (φ j)) :=
  fun D hD => hφ.eventually (h D hD)

/-- The cover lemma for `w.h.p.` (see `RBM.StochDomAt.iff_cover`). -/
theorem iff_cover {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ)
    (Ξ : ℕ → Set Ω₀) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) :
    RBM.Gauss.HighProbAt μ size Ξ ↔
      ∀ k, RBM.Gauss.HighProbAt μ (fun j => size (φ k j)) (fun j => Ξ (φ k j)) := by
  refine ⟨fun h k => subseq μ size Ξ (φ k) (hφ k).tendsto_atTop h, fun h D hD => ?_⟩
  exact RBM.sizesComp_eventually_of_cover φ hφ hcov fun k => h k D hD

end RBM.Gauss.HighProbAt

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

theorem PrecPT_comp_iff (φ : ℕ → ℕ) (hφ : Function.Injective φ) {U : ℕ → Type u}
    (ξ ζ : ∀ j, U j → SeqΩ (sz.comp φ) → ℝ) :
    PrecPT (sz.comp φ) ξ ζ ↔
      RBM.Path.PerTimeDomAt (seqP sz) (fun j => sz.size (φ j)) (U := U)
        (fun j u ω => ξ j u (reindex sz φ ω)) (fun j u ω => ζ j u (reindex sz φ ω)) :=
  RBM.Path.PerTimeDomAt.map_iff (seqP sz) (seqP (sz.comp φ)) (reindex sz φ)
    (seqP_reindex_preimage sz φ hφ) (fun j => sz.size (φ j)) ξ ζ

theorem Whp_comp_iff (φ : ℕ → ℕ) (hφ : Function.Injective φ) (Ξ : ℕ → Set (SeqΩ (sz.comp φ))) :
    Whp (sz.comp φ) Ξ ↔
      RBM.Gauss.HighProbAt (seqP sz) (fun j => sz.size (φ j)) (fun j => reindex sz φ ⁻¹' Ξ j) :=
  RBM.Gauss.HighProbAt.map_iff (seqP sz) (seqP (sz.comp φ)) (reindex sz φ)
    (seqP_reindex_preimage sz φ hφ) (fun j => sz.size (φ j)) Ξ

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

theorem perTimeDomAt_iff_comp_cover (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι]
    (φ : ι → ℕ → ℕ) (ν : ∀ k, Measure (SeqΩ (sz.comp (φ k)))) (hφ : ∀ k, StrictMono (φ k))
    (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k))
    (hlaw : ∀ k (s : Set (SeqΩ (sz.comp (φ k)))), μ (reindex sz (φ k) ⁻¹' s) = ν k s)
    {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ)
    (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (sz.comp (φ k)) → ℝ)
    (hξ : ∀ k j u ω, ξ' k j u (reindex sz (φ k) ω) = ξ (φ k j) u ω)
    (hζ : ∀ k j u ω, ζ' k j u (reindex sz (φ k) ω) = ζ (φ k j) u ω) :
    RBM.Path.PerTimeDomAt μ sz.size ξ ζ ↔
      ∀ k, RBM.Path.PerTimeDomAt (ν k) (sz.comp (φ k)).size (U := fun j => U (φ k j)) (ξ' k)
        (ζ' k) := by
  refine (RBM.Path.PerTimeDomAt.iff_cover μ sz.size ξ ζ φ hφ hcov).trans
    (forall_congr' fun k => ?_)
  have e1 : (fun j u ω => ξ' k j u (reindex sz (φ k) ω)) = fun j => ξ (φ k j) := by
    funext j u ω; exact hξ k j u ω
  have e2 : (fun j u ω => ζ' k j u (reindex sz (φ k) ω)) = fun j => ζ (φ k j) := by
    funext j u ω; exact hζ k j u ω
  have := RBM.Path.PerTimeDomAt.map_iff μ (ν k) (reindex sz (φ k)) (hlaw k) (sz.comp (φ k)).size
    (U := fun j => U (φ k j)) (ξ' k) (ζ' k)
  rw [e1, e2] at this
  exact this.symm

theorem highProbAt_iff_comp_cover (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι]
    (φ : ι → ℕ → ℕ) (ν : ∀ k, Measure (SeqΩ (sz.comp (φ k)))) (hφ : ∀ k, StrictMono (φ k))
    (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k))
    (hlaw : ∀ k (s : Set (SeqΩ (sz.comp (φ k)))), μ (reindex sz (φ k) ⁻¹' s) = ν k s)
    (Ξ : ℕ → Set (SeqΩ sz)) (Ξ' : ∀ k, ℕ → Set (SeqΩ (sz.comp (φ k))))
    (hΞ : ∀ k j, reindex sz (φ k) ⁻¹' Ξ' k j = Ξ (φ k j)) :
    RBM.Gauss.HighProbAt μ sz.size Ξ ↔
      ∀ k, RBM.Gauss.HighProbAt (ν k) (sz.comp (φ k)).size (Ξ' k) := by
  refine (RBM.Gauss.HighProbAt.iff_cover μ sz.size Ξ φ hφ hcov).trans (forall_congr' fun k => ?_)
  have e1 : (fun j => reindex sz (φ k) ⁻¹' Ξ' k j) = fun j => Ξ (φ k j) := by
    funext j; exact hΞ k j
  have := RBM.Gauss.HighProbAt.map_iff μ (ν k) (reindex sz (φ k)) (hlaw k) (sz.comp (φ k)).size
    (Ξ' k)
  rw [e1] at this
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

theorem PrecPT_iff_comp_cover {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (hφ : ∀ k, StrictMono (φ k)) (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k))
    {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ)
    (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (sz.comp (φ k)) → ℝ)
    (hξ : ∀ k j u ω, ξ' k j u (reindex sz (φ k) ω) = ξ (φ k j) u ω)
    (hζ : ∀ k j u ω, ζ' k j u (reindex sz (φ k) ω) = ζ (φ k j) u ω) :
    PrecPT sz ξ ζ ↔ ∀ k, PrecPT (sz.comp (φ k)) (U := fun j => U (φ k j)) (ξ' k) (ζ' k) :=
  perTimeDomAt_iff_comp_cover sz (seqP sz) φ (fun k => seqP (sz.comp (φ k))) hφ hcov
    (fun k s => seqP_reindex_preimage sz (φ k) (hφ k).injective s) ξ ζ ξ' ζ' hξ hζ

theorem Whp_iff_comp_cover {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ) (hφ : ∀ k, StrictMono (φ k))
    (hcov : ∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) (Ξ : ℕ → Set (SeqΩ sz))
    (Ξ' : ∀ k, ℕ → Set (SeqΩ (sz.comp (φ k))))
    (hΞ : ∀ k j, reindex sz (φ k) ⁻¹' Ξ' k j = Ξ (φ k j)) :
    Whp sz Ξ ↔ ∀ k, Whp (sz.comp (φ k)) (Ξ' k) :=
  highProbAt_iff_comp_cover sz (seqP sz) φ (fun k => seqP (sz.comp (φ k))) hφ hcov
    (fun k s => seqP_reindex_preimage sz (φ k) (hφ k).injective s) Ξ Ξ' hΞ

end RBM.Gauss.Sizes

/-! ## 6. The compiled nonempty instances: `d = 3`, `sz0`, `φ = (2 * ·)`

`sz0` (`Defs/Sizes.lean:260`) has `L n = 4 (n+1)`, `W n = (2 (n+1))^5`, `lam n = (2 (n+1))^{-6}`; the
subsequence `φ j = 2 j` is `StrictMono`, injective and tends to infinity.  Every deterministic
hypothesis is discharged; what stays a hypothesis of an instance is a stochastic premise of
`STLK`, `STExp2` (a `Prec` statement). -/

namespace RBM.Gauss.SizesCompInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

theorem two_mul_strictMono : StrictMono (fun j : ℕ => 2 * j) := fun a b h => by
  change 2 * a < 2 * b
  omega

theorem two_mul_tendsto : Tendsto (fun j : ℕ => 2 * j) atTop atTop :=
  two_mul_strictMono.tendsto_atTop

/-- `sz0.comp (2 * ·)` at `j = 1` is `sz0` at `n = 2`. -/
theorem inst_comp_values :
    (sz0.comp (2 * ·)).L 1 = 12 ∧ (sz0.comp (2 * ·)).W 1 = 7776 ∧
      (sz0.comp (2 * ·)).lam 1 = 1 / 46656 := by
  refine ⟨rfl, ?_, ?_⟩
  · norm_num [comp, sz0]
  · norm_num [comp, sz0]

theorem inst_comp_admissible : (sz0.comp (2 * ·)).Admissible (1 / 6) (1 / 10) :=
  comp_admissible sz0 (2 * ·) (1 / 6) (1 / 10) two_mul_tendsto sz0_admissible

theorem inst_flow_comp :
    STFlow (sz0.comp (2 * ·)) (1 / 10) (1 / 10) (1 / 6) (1 / 10) (fun j => z0 (2 * j)) :=
  STFlow_comp sz0 (2 * ·) (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0 two_mul_tendsto flow_z0

theorem inst_conStInd_comp :
    ∀ 𝔠d : ℝ, 0 < 𝔠d →
      STConStInd (sz0.comp (2 * ·)) 𝔠d (fun j => sInst (2 * j)) (fun j => tInst (2 * j)) :=
  fun _ h𝔠d => STConStInd_comp sz0 (2 * ·) _ sInst tInst two_mul_tendsto (conStInd_inst h𝔠d)

theorem inst_reindex_mp :
    MeasurePreserving (reindex sz0 (2 * ·)) (seqP sz0) (seqP (sz0.comp (2 * ·))) :=
  measurePreserving_reindex sz0 (2 * ·) two_mul_strictMono.injective

/-- The block Anderson law `seqP (sz0.withLam 0)`, every set. -/
theorem inst_reindex_BA :
    ∀ s : Set (SeqΩ (sz0.comp (2 * ·))),
      seqP (sz0.withLam 0) (reindex sz0 (2 * ·) ⁻¹' s) = seqP ((sz0.comp (2 * ·)).withLam 0) s :=
  fun s => seqP_withLam_reindex_preimage sz0 (2 * ·) 0 two_mul_strictMono.injective s

/-- A merged `Prec` family (`Lloop`, `STKloop`, `Bctl`) transferred along `φ = 2 *`. -/
theorem inst_STLK_comp :
    STLK sz0 (STflowE z0) sInst →
      STLK (sz0.comp (2 * ·)) (STflowE (fun j => z0 (2 * j))) (fun j => sInst (2 * j)) := by
  intro h k hk
  exact Prec_comp sz0 (2 * ·) two_mul_strictMono _ _ _ _ (fun j u ω => rfl) (fun j u ω => rfl)
    (h k hk)

/-- Helper of `inst_STExp2_comp` for abstract `sz` (the general form belongs to the regime assembly:
T2206 "Not targets"); stated for an abstract `sz` so that no field of `sz0` is unfolded. -/
private theorem sizesComp_STExp2_comp {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (E τ : ℕ → ℝ) (h : STExp2 sz E τ) : STExp2 (sz.comp φ) (fun j => E (φ j)) (fun j => τ (φ j)) := by
  refine Prec_comp sz φ hφ _ _ _ _ (fun j p ω => ?_) (fun j p ω => rfl) h
  exact congrArg (fun x : ℂ => ‖x - STKloop sz (φ j) (E (φ j)) (τ (φ j)) p.1 p.2‖)
    (integral_Lloop_reindex sz φ hφ.injective j (E (φ j)) (τ (φ j)) p.1 p.2)

/-- The deterministic integral side transferred: exercises `integral_Lloop_reindex`. -/
theorem inst_STExp2_comp :
    STExp2 sz0 (STflowE z0) sInst →
      STExp2 (sz0.comp (2 * ·)) (STflowE (fun j => z0 (2 * j))) (fun j => sInst (2 * j)) :=
  fun h => sizesComp_STExp2_comp sz0 (2 * ·) two_mul_strictMono (STflowE z0) sInst h

theorem parity_infinite (r : Fin 2) : {m : ℕ | m % 2 = (r : ℕ)}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2 * n + (r : ℕ))
    (fun a b h => by simpa using h) (fun n => by simp [Nat.add_mod]; omega)

/-- The cover lemma on the two parity classes: `STLK` on `sz0.comp (nth (· % 2 = r))`, `r = 0, 1`,
gives `STLK sz0`. -/
theorem inst_STLK_parity :
    (∀ r : Fin 2,
      STLK (sz0.comp (Nat.nth (fun m => m % 2 = (r : ℕ))))
        (fun j => STflowE z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
        (fun j => sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j))) →
      STLK sz0 (STflowE z0) sInst := by
  intro h k hk
  have hmono : ∀ r : Fin 2, StrictMono (Nat.nth (fun m => m % 2 = (r : ℕ))) :=
    fun r => Nat.nth_strictMono (parity_infinite r)
  have hcov : ∀ᶠ n in atTop, ∃ r : Fin 2, n ∈ Set.range (Nat.nth fun m => m % 2 = (r : ℕ)) :=
    Eventually.of_forall fun n =>
      ⟨⟨n % 2, Nat.mod_lt _ (by norm_num)⟩, by rw [Nat.range_nth_of_infinite (parity_infinite _)]; rfl⟩
  exact (Prec_iff_comp_cover sz0 (fun r : Fin 2 => Nat.nth (fun m => m % 2 = (r : ℕ))) hmono hcov
    _ _ _ _ (fun r j u ω => rfl) (fun r j u ω => rfl)).2 (fun r => h r k hk)

/-! ### Extra instances: the deterministic family `ξ = 0 ≺ ζ = 1`, so that every generic target is applied
at concrete data with nothing left open (the premises of instances 7-9 are stochastic and stay
hypotheses). -/

section Zero

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
private theorem badSetAt_zero (size : ℕ → ℕ) (τ : ℝ) (l : ℕ) :
    badSetAt size (fun (_ : ℕ) (_ : Unit) (_ : Ω) => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) τ l = ∅ := by
  ext ω
  simp only [badSetAt, mul_one, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_lt]
  exact fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem stochDomAt_zero (P : Measure Ω) (size : ℕ → ℕ) :
    RBM.StochDomAt P size (U := fun _ => Unit) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  fun τ _ D _ => Eventually.of_forall fun l => by rw [badSetAt_zero]; simp

private theorem perTimeDomAt_zero (P : Measure Ω) (size : ℕ → ℕ) :
    RBM.Path.PerTimeDomAt P size (U := fun _ => Unit) (fun _ _ _ => (0 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
  fun τ _ D _ => Eventually.of_forall fun l u => by
    have : {ω : Ω | (size l : ℝ) ^ τ * (1 : ℝ) < 0} = ∅ := by
      ext ω
      simp only [mul_one, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    change P {ω : Ω | (size l : ℝ) ^ τ * (1 : ℝ) < 0} ≤ _
    rw [this]
    simp

end Zero

/-- `exact image law` of `≺` at `sz0`: the zero family under `seqP (sz0.comp (2 * ·))` is `≺` iff it is
under `seqP sz0` along `2 *` (`Prec_comp_iff`, both directions of `map_iff`). -/
theorem inst_Prec_comp_iff :
    Prec (sz0.comp (2 * ·)) (U := fun _ => Unit) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) ∧
      RBM.StochDomAt (seqP sz0) (fun j => sz0.size (2 * j)) (U := fun _ => Unit)
        (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  ⟨(Prec_comp_iff sz0 (2 * ·) two_mul_strictMono.injective _ _).2 (stochDomAt_zero _ _),
    stochDomAt_zero _ _⟩

theorem inst_PrecPT_Whp_comp_iff :
    PrecPT (sz0.comp (2 * ·)) (U := fun _ => Unit) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) ∧
      Whp (sz0.comp (2 * ·)) (fun _ => Set.univ) :=
  ⟨(PrecPT_comp_iff sz0 (2 * ·) two_mul_strictMono.injective _ _).2 (perTimeDomAt_zero _ _),
    (Whp_comp_iff sz0 (2 * ·) two_mul_strictMono.injective _).2 (highProbAt_univ _ _)⟩

/-- `of_map`, the cheap direction, at `sz0` (`μ.map (reindex) = seqP (sz0.comp (2 * ·))`): the premise is
a stochastic `≺` statement (nonvacuous: `inst_Prec_comp_iff` shows it holds for `ξ = 0`, `ζ = 1`). -/
theorem inst_of_map (ξ ζ : ℕ → Unit → SeqΩ (sz0.comp (2 * ·)) → ℝ)
    (h : Prec (sz0.comp (2 * ·)) ξ ζ) :
    RBM.StochDomAt (seqP sz0) (sz0.comp (2 * ·)).size (U := fun _ => Unit)
      (fun l u ω => ξ l u (reindex sz0 (2 * ·) ω)) (fun l u ω => ζ l u (reindex sz0 (2 * ·) ω)) :=
  RBM.StochDomAt.of_map (seqP sz0) (seqP (sz0.comp (2 * ·))) (reindex sz0 (2 * ·))
    (measurable_reindex sz0 _) inst_reindex_mp.map_eq (sz0.comp (2 * ·)).size ξ ζ h

/-- `subseq` at `sz0`, for the three predicates. -/
theorem inst_subseq :
    RBM.StochDomAt (seqP sz0) (fun j => sz0.size (2 * j)) (U := fun _ => Unit)
        (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) ∧
      RBM.Path.PerTimeDomAt (seqP sz0) (fun j => sz0.size (2 * j)) (U := fun _ => Unit)
        (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) ∧
      RBM.Gauss.HighProbAt (seqP sz0) (fun j => sz0.size (2 * j)) (fun _ => Set.univ) :=
  ⟨RBM.StochDomAt.subseq (seqP sz0) sz0.size (U := fun _ => Unit) (fun _ _ _ => (0 : ℝ))
      (fun _ _ _ => (1 : ℝ)) (2 * ·) two_mul_tendsto (stochDomAt_zero _ _),
    RBM.Path.PerTimeDomAt.subseq (seqP sz0) sz0.size (U := fun _ => Unit) (fun _ _ _ => (0 : ℝ))
      (fun _ _ _ => (1 : ℝ)) (2 * ·) two_mul_tendsto (perTimeDomAt_zero _ _),
    RBM.Gauss.HighProbAt.subseq (seqP sz0) sz0.size (fun _ => Set.univ) (2 * ·) two_mul_tendsto
      (highProbAt_univ _ _)⟩

/-- `nth_cover` for the parity partition `c m = m % 2` of `ℕ` into two infinite classes. -/
theorem inst_nth_cover :
    ∀ᶠ n in atTop, ∃ i : {i : Fin 2 // {m : ℕ | (⟨m % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = i}.Infinite},
      n ∈ Set.range (Nat.nth (fun m => (⟨m % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = i.1)) :=
  nth_cover (fun m : ℕ => (⟨m % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))

/-- The three cover composites on the parity classes for the deterministic family, glued back to
`PrecPT sz0` and `Whp sz0`. -/
theorem inst_parity_PrecPT_Whp :
    PrecPT sz0 (U := fun _ => Unit) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) ∧
      Whp sz0 (fun _ => Set.univ) := by
  have hmono : ∀ r : Fin 2, StrictMono (Nat.nth (fun m => m % 2 = (r : ℕ))) :=
    fun r => Nat.nth_strictMono (parity_infinite r)
  have hcov : ∀ᶠ n in atTop, ∃ r : Fin 2, n ∈ Set.range (Nat.nth fun m => m % 2 = (r : ℕ)) :=
    Eventually.of_forall fun n =>
      ⟨⟨n % 2, Nat.mod_lt _ (by norm_num)⟩, by rw [Nat.range_nth_of_infinite (parity_infinite _)]; rfl⟩
  refine ⟨(PrecPT_iff_comp_cover sz0 (fun r : Fin 2 => Nat.nth (fun m => m % 2 = (r : ℕ))) hmono hcov
      (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ _ => (0 : ℝ)) (fun _ _ _ _ => (1 : ℝ))
      (fun r j u ω => rfl) (fun r j u ω => rfl)).2 fun r => ?_,
    (Whp_iff_comp_cover sz0 (fun r : Fin 2 => Nat.nth (fun m => m % 2 = (r : ℕ))) hmono hcov
      (fun _ => Set.univ) (fun _ _ => Set.univ) (fun r j => rfl)).2 fun r => ?_⟩
  · exact perTimeDomAt_zero _ _
  · exact highProbAt_univ _ _

end RBM.Gauss.SizesCompInst
