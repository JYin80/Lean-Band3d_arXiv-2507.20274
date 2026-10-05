/-
Release check for T2206 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20, §29, §45 O2, §67, §68 (8)).
ST-A: the generic subsequence transfer of route (A) (supervisor `docs/supervisor/2026-10-05-1806.md`, answers to
REQ-2026-10-05-1746, Q1 "(A), one generic ticket"): `Sizes.comp φ`, the reindexing `SeqΩ sz → SeqΩ (sz.comp φ)`, its
measure preservation (and the exact image law: all sets, all integrands), the per-`n` objects commuting with it, the
transfer of `≺` (`Prec`, `PrecPT`, `Whp`, and law-generic `StochDomAt`, `PerTimeDomAt`, `HighProbAt`), and the cover lemma
for finite partitions of `ℕ`.
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 3429d7d) and of the Mathlib lemmas the
preflight names (their modules are imported explicitly below; `import RBM3D` is not relied on for them).
Section 2: the two vocabulary defs `comp_voc`, `reindex_voc` (the library defines `RBM.Gauss.Sizes.comp` and
`RBM.Gauss.Sizes.reindex` with exactly these bodies, docstrings added).
Section 3: the pins (`def … _pin : Prop`), one per public theorem of the new file; each theorem's type is the pin body with
`comp_voc` read as `Sizes.comp` and `reindex_voc` as `Sizes.reindex` (binder order included).
Section 4: Prop-valued examples at `sz0`, `φ = (2 * ·)` (the statements of the instances; no proof obligation).
No theorem, no proof, no placeholder, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2206-check.lean`.
-/
import RBM3D
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Data.Nat.Nth
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! ## 1. Merged names -/

-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_admissible
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.Sizes.SeqCoord
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqGvar
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.measurable_slice
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.measurable_seqHflow_entry
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.STGM
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STLocalMax
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STMainInd
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.conStInd_inst
-- `RBM3D/Defs/Params.lean` (c3f3d5d), `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.zt
#check @RBM.lemE
#check @RBM.lemT
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.badSetAt
#check @RBM.StochDomAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.Whp
#check @RBM.StochDomAt.of_subset
#check @RBM.StochDomAt.precomp_param
-- `RBM3D/Path/Walk.lean` (ddf5f74): `PrecGrid` not in scope (the grid carrier `pathP`), cited only; the measurability
-- of `Gt` entries and `Lloop` (the alternative route for `integral_Lloop_reindex`, preflight (ii))
#check @RBM.Gauss.Sizes.PrecGrid
#check @RBM.Gauss.Sizes.walk_measurable_Gt_apply
#check @RBM.Gauss.Sizes.walk_measurable_Lloop

-- Mathlib (the preflight's routes)
#check @MeasureTheory.Measure.infinitePi
#check @MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj
#check @MeasureTheory.Measure.infinitePi_map_restrict'
#check @MeasureTheory.Measure.infinitePi_map_piCongrLeft
#check @MeasureTheory.Measure.infinitePi_pi
#check @MeasureTheory.Measure.eq_infinitePi
#check @ProbabilityTheory.iIndepFun_infinitePi
#check @ProbabilityTheory.indep_iSup_of_disjoint
#check @ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map
#check @MeasurableEquiv.piEquivPiSubtypeProd
#check @MeasurableEquiv.map_apply
#check @MeasureTheory.Measure.le_map_apply
#check @MeasureTheory.Measure.prod_prod
#check @MeasureTheory.integral_fun_fst
#check @MeasureTheory.integral_map_equiv
#check @Nat.nth
#check @Nat.nth_strictMono
#check @Nat.range_nth_of_infinite
#check @Nat.nth_mem_of_infinite
#check @StrictMono.tendsto_atTop
#check @Filter.Tendsto.eventually

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

universe u v w u'

namespace RBM.Gauss.Sizes.T2206Check

/-! ## 2. Vocabulary (the library: `RBM.Gauss.Sizes.comp`, `RBM.Gauss.Sizes.reindex`) -/

/-- The sizes along `φ`: the five fields of `Sizes` composed with `φ`. -/
def comp_voc {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) : Sizes d where
  L := fun j => sz.L (φ j)
  W := fun j => sz.W (φ j)
  lam := fun j => sz.lam (φ j)
  three_le_L := fun j => sz.three_le_L (φ j)
  W_pos := fun j => sz.W_pos (φ j)

/-- The reindexing of the common sample space: `ω ↦ (⟨j, c⟩ ↦ ω ⟨φ j, c⟩)`. -/
def reindex_voc {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (ω : SeqΩ sz) : SeqΩ (comp_voc sz φ) :=
  fun p => ω ⟨φ p.1, p.2⟩

/-! ## 3. The pins -/

/-! ### 3a. `Sizes.comp`: fields and the transfer of the eventual / pointwise predicates (`Tendsto φ atTop atTop`) -/

def comp_L_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ), (comp_voc sz φ).L j = sz.L (φ j)

def comp_W_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ), (comp_voc sz φ).W j = sz.W (φ j)

def comp_lam_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ), (comp_voc sz φ).lam j = sz.lam (φ j)

def comp_size_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ), (comp_voc sz φ).size j = sz.size (φ j)

def withLam_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (g : ℕ → ℝ) (φ : ℕ → ℕ),
    comp_voc (Sizes.withLam sz g) φ = Sizes.withLam (comp_voc sz φ) (fun j => g (φ j))

def comp_locDomain_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (κ ε : ℝ) (j : ℕ) (z : ℂ),
    (comp_voc sz φ).locDomain κ ε j z ↔ sz.locDomain κ ε (φ j) z

def comp_sizeTendsto_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Tendsto φ atTop atTop →
    sz.SizeTendsto → (comp_voc sz φ).SizeTendsto

def comp_bandwidth_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (𝔠 : ℝ), Tendsto φ atTop atTop →
    sz.Bandwidth 𝔠 → (comp_voc sz φ).Bandwidth 𝔠

def comp_WO_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (𝔡 : ℝ), Tendsto φ atTop atTop →
    sz.WO 𝔡 → (comp_voc sz φ).WO 𝔡

def comp_admissible_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (𝔠 𝔡 : ℝ), Tendsto φ atTop atTop →
    sz.Admissible 𝔠 𝔡 → (comp_voc sz φ).Admissible 𝔠 𝔡

def STFlow_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Tendsto φ atTop atTop →
    STFlow sz κ ε 𝔠 𝔡 z → STFlow (comp_voc sz φ) κ ε 𝔠 𝔡 (fun j => z (φ j))

def STConStInd_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (𝔠d : ℝ) (s t : ℕ → ℝ), Tendsto φ atTop atTop →
    STConStInd sz 𝔠d s t → STConStInd (comp_voc sz φ) 𝔠d (fun j => s (φ j)) (fun j => t (φ j))

/-! ### 3b. The reindexing and the laws (`Function.Injective φ` for the laws) -/

def measurable_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Measurable (reindex_voc sz φ)

def measurePreserving_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Function.Injective φ →
    MeasurePreserving (reindex_voc sz φ) (seqP sz) (seqP (comp_voc sz φ))

/-- Generic: an injective reindexing of an `infinitePi` has the reindexed product as its **exact** image law, on every set
(measurable or not). -/
def infinitePi_preimage_comp_pin : Prop :=
  ∀ {ι : Type u} {α : Type v} {X : ι → Type w} [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : α → ι), Function.Injective f →
    ∀ s : Set (∀ a, X (f a)),
      Measure.infinitePi μ ((fun (ω : ∀ i, X i) (a : α) => ω (f a)) ⁻¹' s) =
        Measure.infinitePi (fun a => μ (f a)) s

/-- Generic: the same for integrals, every integrand (no measurability). -/
def integral_infinitePi_comp_pin : Prop :=
  ∀ {ι : Type u} {α : Type v} {X : ι → Type w} [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : α → ι), Function.Injective f →
    ∀ {E : Type u'} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : (∀ a, X (f a)) → E),
      MeasureTheory.integral (Measure.infinitePi μ) (fun ω : (∀ i, X i) => g (fun a => ω (f a))) =
        MeasureTheory.integral (Measure.infinitePi (fun a => μ (f a))) g

def seqP_reindex_preimage_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Function.Injective φ →
    ∀ s : Set (SeqΩ (comp_voc sz φ)), seqP sz (reindex_voc sz φ ⁻¹' s) = seqP (comp_voc sz φ) s

/-- The block Anderson law `(sz.withLam g).seqP` (`g = 0`), on the same sample space `SeqΩ sz`. -/
def seqP_withLam_reindex_preimage_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (g : ℕ → ℝ), Function.Injective φ →
    ∀ s : Set (SeqΩ (comp_voc sz φ)),
      seqP (Sizes.withLam sz g) (reindex_voc sz φ ⁻¹' s) =
        seqP (Sizes.withLam (comp_voc sz φ) (fun j => g (φ j))) s

def integral_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Function.Injective φ →
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : SeqΩ (comp_voc sz φ) → E),
      MeasureTheory.integral (seqP sz) (fun ω => g (reindex_voc sz φ ω)) =
        MeasureTheory.integral (seqP (comp_voc sz φ)) g

/-! ### 3c. The per-`n` objects commute with the reindexing (expected: `rfl`, except the integral) -/

def slice_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (ω : SeqΩ sz),
    slice (comp_voc sz φ) j (reindex_voc sz φ ω) = slice sz (φ j) ω

def seqXmat_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (ω : SeqΩ sz),
    seqXmat (comp_voc sz φ) j (reindex_voc sz φ ω) = seqXmat sz (φ j) ω

def seqHflow_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (u : ℝ) (ω : SeqΩ sz),
    seqHflow (comp_voc sz φ) j u (reindex_voc sz φ ω) = seqHflow sz (φ j) u ω

def Gt_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (E t : ℝ) (σ : Bool) (ω : SeqΩ sz),
    Gt (comp_voc sz φ) j E t σ (reindex_voc sz φ ω) = Gt sz (φ j) E t σ ω

def Lloop_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (E t : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → RBM.Zd d (sz.L (φ j))) (ω : SeqΩ sz),
    Lloop (comp_voc sz φ) j E t σ a (reindex_voc sz φ ω) = Lloop sz (φ j) E t σ a ω

def STGM_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (E τ : ℝ) (ω : SeqΩ sz)
    (x y : RBM.Gauss.Idx d (sz.L (φ j)) (sz.W (φ j))),
    STGM (comp_voc sz φ) j E τ (reindex_voc sz φ ω) x y = STGM sz (φ j) E τ ω x y

def STKloop_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (E τ : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → RBM.Zd d (sz.L (φ j))),
    STKloop (comp_voc sz φ) j E τ σ a = STKloop sz (φ j) E τ σ a

def Bctl_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (t : ℝ), (comp_voc sz φ).Bctl j t = sz.Bctl (φ j) t

def STWB_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (τ : ℝ) (K : ℕ),
    STWB (comp_voc sz φ) j τ K = STWB sz (φ j) τ K

def STblk_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (x : RBM.Gauss.Idx d (sz.L (φ j)) (sz.W (φ j))),
    STblk (comp_voc sz φ) j x = STblk sz (φ j) x

def ellT_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ) (j : ℕ) (τ : ℝ),
    RBM.ellT ((comp_voc sz φ).L j) ((comp_voc sz φ).lam j) τ = RBM.ellT (sz.L (φ j)) (sz.lam (φ j)) τ

def STflowE_comp_pin : Prop :=
  ∀ (z : ℕ → ℂ) (φ : ℕ → ℕ), STflowE (fun j => z (φ j)) = fun j => STflowE z (φ j)

/-- The deterministic left side of `STExp2` (`Induction/Defs.lean:159`) integrates over the whole law. -/
def integral_Lloop_reindex_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Function.Injective φ →
    ∀ (j : ℕ) (E t : ℝ) {m : ℕ} (σ : Fin m → Bool) (a : Fin m → RBM.Zd d (sz.L (φ j))),
      MeasureTheory.integral (seqP (comp_voc sz φ)) (fun ω => Lloop (comp_voc sz φ) j E t σ a ω) =
        MeasureTheory.integral (seqP sz) (fun ω => Lloop sz (φ j) E t σ a ω)

/-! ### 3d. `≺` at an arbitrary law: image laws, subsequences, finite covers (namespaces `RBM`, `RBM.Path`, `RBM.Gauss`) -/

def StochDomAt_map_iff_pin : Prop :=
  ∀ {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] (μ : Measure Ω₀) (ν : Measure Ω₁)
    (f : Ω₀ → Ω₁), (∀ s : Set Ω₁, μ (f ⁻¹' s) = ν s) →
    ∀ (size : ℕ → ℕ) {U : ℕ → Type w} (ξ ζ : ∀ l, U l → Ω₁ → ℝ),
      RBM.StochDomAt ν size ξ ζ ↔
        RBM.StochDomAt μ size (U := U) (fun l u ω => ξ l u (f ω)) (fun l u ω => ζ l u (f ω))

def PerTimeDomAt_map_iff_pin : Prop :=
  ∀ {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] (μ : Measure Ω₀) (ν : Measure Ω₁)
    (f : Ω₀ → Ω₁), (∀ s : Set Ω₁, μ (f ⁻¹' s) = ν s) →
    ∀ (size : ℕ → ℕ) {U : ℕ → Type w} (ξ ζ : ∀ l, U l → Ω₁ → ℝ),
      RBM.Path.PerTimeDomAt ν size ξ ζ ↔
        RBM.Path.PerTimeDomAt μ size (U := U) (fun l u ω => ξ l u (f ω)) (fun l u ω => ζ l u (f ω))

def HighProbAt_map_iff_pin : Prop :=
  ∀ {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] (μ : Measure Ω₀) (ν : Measure Ω₁)
    (f : Ω₀ → Ω₁), (∀ s : Set Ω₁, μ (f ⁻¹' s) = ν s) →
    ∀ (size : ℕ → ℕ) (Ξ : ℕ → Set Ω₁),
      RBM.Gauss.HighProbAt ν size Ξ ↔ RBM.Gauss.HighProbAt μ size (fun l => f ⁻¹' Ξ l)

/-- The cheap direction: a measurable `f` with `μ.map f = ν` suffices (`Measure.le_map_apply`). -/
def StochDomAt_of_map_pin : Prop :=
  ∀ {Ω₀ : Type u} {Ω₁ : Type v} [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] (μ : Measure Ω₀) (ν : Measure Ω₁)
    (f : Ω₀ → Ω₁), Measurable f → μ.map f = ν →
    ∀ (size : ℕ → ℕ) {U : ℕ → Type w} (ξ ζ : ∀ l, U l → Ω₁ → ℝ),
      RBM.StochDomAt ν size ξ ζ →
        RBM.StochDomAt μ size (U := U) (fun l u ω => ξ l u (f ω)) (fun l u ω => ζ l u (f ω))

def StochDomAt_subseq_pin : Prop :=
  ∀ {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) {U : ℕ → Type v}
    (ξ ζ : ∀ l, U l → Ω₀ → ℝ) (φ : ℕ → ℕ), Tendsto φ atTop atTop →
    RBM.StochDomAt μ size ξ ζ →
      RBM.StochDomAt μ (fun j => size (φ j)) (U := fun j => U (φ j)) (fun j => ξ (φ j)) (fun j => ζ (φ j))

def PerTimeDomAt_subseq_pin : Prop :=
  ∀ {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) {U : ℕ → Type v}
    (ξ ζ : ∀ l, U l → Ω₀ → ℝ) (φ : ℕ → ℕ), Tendsto φ atTop atTop →
    RBM.Path.PerTimeDomAt μ size ξ ζ →
      RBM.Path.PerTimeDomAt μ (fun j => size (φ j)) (U := fun j => U (φ j)) (fun j => ξ (φ j))
        (fun j => ζ (φ j))

def HighProbAt_subseq_pin : Prop :=
  ∀ {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) (Ξ : ℕ → Set Ω₀) (φ : ℕ → ℕ),
    Tendsto φ atTop atTop →
    RBM.Gauss.HighProbAt μ size Ξ → RBM.Gauss.HighProbAt μ (fun j => size (φ j)) (fun j => Ξ (φ j))

/-- The cover lemma: finitely many strictly increasing enumerations whose ranges contain every large `n`. -/
def StochDomAt_iff_cover_pin : Prop :=
  ∀ {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) {U : ℕ → Type v}
    (ξ ζ : ∀ l, U l → Ω₀ → ℝ) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (RBM.StochDomAt μ size ξ ζ ↔
      ∀ k, RBM.StochDomAt μ (fun j => size (φ k j)) (U := fun j => U (φ k j)) (fun j => ξ (φ k j))
        (fun j => ζ (φ k j)))

def PerTimeDomAt_iff_cover_pin : Prop :=
  ∀ {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) {U : ℕ → Type v}
    (ξ ζ : ∀ l, U l → Ω₀ → ℝ) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (RBM.Path.PerTimeDomAt μ size ξ ζ ↔
      ∀ k, RBM.Path.PerTimeDomAt μ (fun j => size (φ k j)) (U := fun j => U (φ k j)) (fun j => ξ (φ k j))
        (fun j => ζ (φ k j)))

def HighProbAt_iff_cover_pin : Prop :=
  ∀ {Ω₀ : Type u} [MeasurableSpace Ω₀] (μ : Measure Ω₀) (size : ℕ → ℕ) (Ξ : ℕ → Set Ω₀)
    {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (RBM.Gauss.HighProbAt μ size Ξ ↔ ∀ k, RBM.Gauss.HighProbAt μ (fun j => size (φ k j)) (fun j => Ξ (φ k j)))

/-- A finite partition of `ℕ` gives a cover by the `Nat.nth` enumerations of its infinite classes (the finite classes are
bounded, so they do not matter for eventual statements). -/
def nth_cover_pin : Prop :=
  ∀ {ι : Type w} [Finite ι] (c : ℕ → ι),
    ∀ᶠ n in atTop, ∃ i : {i : ι // {m : ℕ | c m = i}.Infinite}, n ∈ Set.range (Nat.nth (fun m => c m = i.1))

/-! ### 3e. `≺` of the chain under `Sizes.comp` -/

/-- Exact pullback (`Function.Injective φ`): `≺` on the subsequence sizes is `≺` on the original law along `φ`. -/
def Prec_comp_iff_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Function.Injective φ →
    ∀ {U : ℕ → Type u} (ξ ζ : ∀ j, U j → SeqΩ (comp_voc sz φ) → ℝ),
      Prec (comp_voc sz φ) ξ ζ ↔
        RBM.StochDomAt (seqP sz) (fun j => sz.size (φ j)) (U := U)
          (fun j u ω => ξ j u (reindex_voc sz φ ω)) (fun j u ω => ζ j u (reindex_voc sz φ ω))

def PrecPT_comp_iff_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Function.Injective φ →
    ∀ {U : ℕ → Type u} (ξ ζ : ∀ j, U j → SeqΩ (comp_voc sz φ) → ℝ),
      PrecPT (comp_voc sz φ) ξ ζ ↔
        RBM.Path.PerTimeDomAt (seqP sz) (fun j => sz.size (φ j)) (U := U)
          (fun j u ω => ξ j u (reindex_voc sz φ ω)) (fun j u ω => ζ j u (reindex_voc sz φ ω))

def Whp_comp_iff_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), Function.Injective φ →
    ∀ (Ξ : ℕ → Set (SeqΩ (comp_voc sz φ))),
      Whp (comp_voc sz φ) Ξ ↔
        RBM.Gauss.HighProbAt (seqP sz) (fun j => sz.size (φ j)) (fun j => reindex_voc sz φ ⁻¹' Ξ j)

/-- Forward along one subsequence, for families that commute with the reindexing. -/
def Prec_comp_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (φ : ℕ → ℕ), StrictMono φ →
    ∀ {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ) (ξ' ζ' : ∀ j, U (φ j) → SeqΩ (comp_voc sz φ) → ℝ),
      (∀ j u ω, ξ' j u (reindex_voc sz φ ω) = ξ (φ j) u ω) →
      (∀ j u ω, ζ' j u (reindex_voc sz φ ω) = ζ (φ j) u ω) →
      Prec sz ξ ζ → Prec (comp_voc sz φ) (U := fun j => U (φ j)) ξ' ζ'

/-- Law-generic gluing (the `PrecL` form of the held T2197, `StochDomAt μ sz.size`, stated without that name). -/
def stochDomAt_iff_comp_cover_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (ν : ∀ k, Measure (SeqΩ (comp_voc sz (φ k)))),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (∀ k (s : Set (SeqΩ (comp_voc sz (φ k)))), μ (reindex_voc sz (φ k) ⁻¹' s) = ν k s) →
    ∀ {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ)
      (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (comp_voc sz (φ k)) → ℝ),
      (∀ k j u ω, ξ' k j u (reindex_voc sz (φ k) ω) = ξ (φ k j) u ω) →
      (∀ k j u ω, ζ' k j u (reindex_voc sz (φ k) ω) = ζ (φ k j) u ω) →
      (RBM.StochDomAt μ sz.size ξ ζ ↔
        ∀ k, RBM.StochDomAt (ν k) (comp_voc sz (φ k)).size (U := fun j => U (φ k j)) (ξ' k) (ζ' k))

def perTimeDomAt_iff_comp_cover_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (ν : ∀ k, Measure (SeqΩ (comp_voc sz (φ k)))),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (∀ k (s : Set (SeqΩ (comp_voc sz (φ k)))), μ (reindex_voc sz (φ k) ⁻¹' s) = ν k s) →
    ∀ {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ)
      (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (comp_voc sz (φ k)) → ℝ),
      (∀ k j u ω, ξ' k j u (reindex_voc sz (φ k) ω) = ξ (φ k j) u ω) →
      (∀ k j u ω, ζ' k j u (reindex_voc sz (φ k) ω) = ζ (φ k j) u ω) →
      (RBM.Path.PerTimeDomAt μ sz.size ξ ζ ↔
        ∀ k, RBM.Path.PerTimeDomAt (ν k) (comp_voc sz (φ k)).size (U := fun j => U (φ k j)) (ξ' k) (ζ' k))

def highProbAt_iff_comp_cover_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (μ : Measure (SeqΩ sz)) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ)
    (ν : ∀ k, Measure (SeqΩ (comp_voc sz (φ k)))),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    (∀ k (s : Set (SeqΩ (comp_voc sz (φ k)))), μ (reindex_voc sz (φ k) ⁻¹' s) = ν k s) →
    ∀ (Ξ : ℕ → Set (SeqΩ sz)) (Ξ' : ∀ k, ℕ → Set (SeqΩ (comp_voc sz (φ k)))),
      (∀ k j, reindex_voc sz (φ k) ⁻¹' Ξ' k j = Ξ (φ k j)) →
      (RBM.Gauss.HighProbAt μ sz.size Ξ ↔ ∀ k, RBM.Gauss.HighProbAt (ν k) (comp_voc sz (φ k)).size (Ξ' k))

/-- The model law: what the main-induction regime gluing uses (premises `sz → sz.comp φ k`, conclusions back). -/
def Prec_iff_comp_cover_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    ∀ {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ)
      (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (comp_voc sz (φ k)) → ℝ),
      (∀ k j u ω, ξ' k j u (reindex_voc sz (φ k) ω) = ξ (φ k j) u ω) →
      (∀ k j u ω, ζ' k j u (reindex_voc sz (φ k) ω) = ζ (φ k j) u ω) →
      (Prec sz ξ ζ ↔ ∀ k, Prec (comp_voc sz (φ k)) (U := fun j => U (φ k j)) (ξ' k) (ζ' k))

def PrecPT_iff_comp_cover_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    ∀ {U : ℕ → Type u} (ξ ζ : ∀ n, U n → SeqΩ sz → ℝ)
      (ξ' ζ' : ∀ k j, U (φ k j) → SeqΩ (comp_voc sz (φ k)) → ℝ),
      (∀ k j u ω, ξ' k j u (reindex_voc sz (φ k) ω) = ξ (φ k j) u ω) →
      (∀ k j u ω, ζ' k j u (reindex_voc sz (φ k) ω) = ζ (φ k j) u ω) →
      (PrecPT sz ξ ζ ↔ ∀ k, PrecPT (comp_voc sz (φ k)) (U := fun j => U (φ k j)) (ξ' k) (ζ' k))

def Whp_iff_comp_cover_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {ι : Type w} [Finite ι] (φ : ι → ℕ → ℕ),
    (∀ k, StrictMono (φ k)) → (∀ᶠ n in atTop, ∃ k, n ∈ Set.range (φ k)) →
    ∀ (Ξ : ℕ → Set (SeqΩ sz)) (Ξ' : ∀ k, ℕ → Set (SeqΩ (comp_voc sz (φ k)))),
      (∀ k j, reindex_voc sz (φ k) ⁻¹' Ξ' k j = Ξ (φ k j)) →
      (Whp sz Ξ ↔ ∀ k, Whp (comp_voc sz (φ k)) (Ξ' k))

/-! ## 4. Instance statements at `sz0`, `φ = (2 * ·)` (no proof obligation) -/

-- `inst_comp_values`: `L = 12`, `W = 6^5`, `lam = 6^{-6}` at `j = 1` (`sz0` at `n = 2`)
example : Prop :=
  (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)).L 1 = 12 ∧ (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)).W 1 = 7776 ∧
    (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)).lam 1 = 1 / 46656
-- `inst_comp_admissible`
example : Prop := (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)).Admissible (1 / 6) (1 / 10)
-- `inst_flow_comp`
example : Prop :=
  STFlow (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)) (1 / 10) (1 / 10) (1 / 6) (1 / 10)
    (fun j => RBM.Gauss.InductionDefsInst.z0 (2 * j))
-- `inst_conStInd_comp`
example : Prop :=
  ∀ 𝔠d : ℝ, 0 < 𝔠d →
    STConStInd (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)) 𝔠d (fun j => RBM.Gauss.InductionDefsInst.sInst (2 * j))
      (fun j => RBM.Gauss.InductionDefsInst.tInst (2 * j))
-- `inst_reindex_mp`
example : Prop :=
  MeasurePreserving (reindex_voc RBM.Gauss.SizesInst.sz0 (2 * ·)) (seqP RBM.Gauss.SizesInst.sz0)
    (seqP (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)))
-- `inst_reindex_BA`: the block Anderson law
example : Prop :=
  ∀ s : Set (SeqΩ (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·))),
    seqP (Sizes.withLam RBM.Gauss.SizesInst.sz0 0) (reindex_voc RBM.Gauss.SizesInst.sz0 (2 * ·) ⁻¹' s) =
      seqP (Sizes.withLam (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)) 0) s
-- `inst_STLK_comp`: a merged `Prec` family (`Lloop`, `STKloop`, `Bctl`) transferred
example : Prop :=
  STLK RBM.Gauss.SizesInst.sz0 (STflowE RBM.Gauss.InductionDefsInst.z0) RBM.Gauss.InductionDefsInst.sInst →
    STLK (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)) (STflowE (fun j => RBM.Gauss.InductionDefsInst.z0 (2 * j)))
      (fun j => RBM.Gauss.InductionDefsInst.sInst (2 * j))
-- `inst_STExp2_comp`: the deterministic integral side transferred
example : Prop :=
  STExp2 RBM.Gauss.SizesInst.sz0 (STflowE RBM.Gauss.InductionDefsInst.z0) RBM.Gauss.InductionDefsInst.sInst →
    STExp2 (comp_voc RBM.Gauss.SizesInst.sz0 (2 * ·)) (STflowE (fun j => RBM.Gauss.InductionDefsInst.z0 (2 * j)))
      (fun j => RBM.Gauss.InductionDefsInst.sInst (2 * j))
-- `inst_STLK_parity`: the cover lemma on the two parity classes
example : Prop :=
  (∀ r : Fin 2,
    STLK (comp_voc RBM.Gauss.SizesInst.sz0 (Nat.nth (fun m => m % 2 = (r : ℕ))))
      (fun j => STflowE RBM.Gauss.InductionDefsInst.z0 (Nat.nth (fun m => m % 2 = (r : ℕ)) j))
      (fun j => RBM.Gauss.InductionDefsInst.sInst (Nat.nth (fun m => m % 2 = (r : ℕ)) j))) →
    STLK RBM.Gauss.SizesInst.sz0 (STflowE RBM.Gauss.InductionDefsInst.z0) RBM.Gauss.InductionDefsInst.sInst

end RBM.Gauss.Sizes.T2206Check

end
