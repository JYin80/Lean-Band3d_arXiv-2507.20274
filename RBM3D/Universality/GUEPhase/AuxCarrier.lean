/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.PinsK
import RBM3D.Universality.OU
import RBM3D.Green.IBP
import RBM3D.Induction.ConArgDet
import RBM3D.Gauss.Domination

/-!
# The auxiliary carrier and the row-chaos (LDE) layer of the GUE phase (T2196, UN-25)

Port of `RBM2D/Universality/GUEPhase/AuxCarrier.lean` at `c9a24cf` (1183 lines) to `d`
dimensions, written model-generically (DECISIONS §57 (2)): any tag-free variance family `v`, the
profile coupling `g` and a deterministic Hermitian shift `A`.

* §2 the auxiliary carrier `auxSizes d` (`L' ≡ 3`, `W' s = max 1 (s / 3)`, `lam' ≡ 0`), the
  coordinatewise embedding of the fine lattice `Idx d L W` into the first block of the auxiliary
  lattice, positivity of the auxiliary variance on one block (`svarF_pos_of_block_eq`, from
  `sbKernelR d L g 0 = (1 + 2 d g²)⁻¹`, valid for every `d` and `g`; RBM2D used `0 ∈ sbSupport 3`),
  and the realisation of an arbitrary variance family by the rescaled auxiliary sample
  (`auxT_law`, `auxHG_law`, `exists_seqP_map_eq_gaussLaw`).
* §3 the law `gaussLaw v`, the mixture variance `mixVar d L W g a b` and its row-sum profile `Smix`.
* §6b the Hanson-Wright tail `chaos_tail` for an arbitrary merged `RowChaos`.
* §6c the quadratic row chaos `auxQuadChaos` of `A + X` at row `i` for a deterministic Hermitian `A`
  (the minor of `A + X` reads no coordinate of row `i`), its identification with the centred
  quadratic form of (4.7), and the tails `gaussLaw_quad_tail` (any tag-free family, any Hermitian
  shift), `gue_quad_tail` (`A = 0`, GUE rows) and `kind_quad_tail` (model class `UNKind`).
* the rank-one row chaos `auxLinChaos` and its tail `aux_lin_tail`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss
open scoped NNReal ENNReal

/-! ## §2 Route (a): the auxiliary carrier, positive on the image of the embedding -/

section Aux

/-- The auxiliary sizes of RBM1D `gueEntryDG` (`GUEPhaseEntry.lean:58`): `L ≡ 3`,
`W s = max 1 (s / 3)`; the coupling is `lam ≡ 0` (`S^(B)(0) = I`; any constant works). -/
def auxSizes (d : ℕ) : Sizes d where
  L _ := 3
  W s := max 1 (s / 3)
  lam _ := 0
  three_le_L _ := le_rfl
  W_pos _ := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)

/-- The slot of the auxiliary model used for a fixed size `(L, W)`: `3 · (W L)`, so that the
auxiliary block side is `(auxSizes d).W slot = W L`. -/
def auxSlot (L W : ℕ) : ℕ := 3 * (W * L)

theorem auxW_slot (d L W : ℕ) [NeZero L] [NeZero W] :
    (auxSizes d).W (auxSlot L W) = W * L := by
  have hpos : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
  change max 1 (3 * (W * L) / 3) = W * L
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]
  omega

theorem auxL (d : ℕ) (_s : ℕ) : (auxSizes d).L _s = 3 := rfl

/-- One coordinate of the embedding: `Z_{WL}` sits in the first block of `Z_{3 (W L)}` (block
side `W L`). -/
def auxEmb1 (d L W : ℕ) [NeZero L] [NeZero W] (a : ZMod (W * L)) :
    ZMod ((auxSizes d).W (auxSlot L W) * (auxSizes d).L (auxSlot L W)) :=
  ((a.val : ℕ) : ZMod ((auxSizes d).W (auxSlot L W) * (auxSizes d).L (auxSlot L W)))

theorem auxEmb1_val (d L W : ℕ) [NeZero L] [NeZero W] (a : ZMod (W * L)) :
    (auxEmb1 d L W a).val = a.val := by
  unfold auxEmb1
  apply ZMod.val_natCast_of_lt
  have h1 := ZMod.val_lt a
  rw [auxW_slot, auxL]
  nlinarith

theorem auxEmb1_injective (d L W : ℕ) [NeZero L] [NeZero W] :
    Function.Injective (auxEmb1 d L W) := by
  intro a b h
  have := congrArg ZMod.val h
  rw [auxEmb1_val, auxEmb1_val] at this
  exact ZMod.val_injective _ this

theorem blk_auxEmb1 (d L W : ℕ) [NeZero L] [NeZero W] (a : ZMod (W * L)) :
    blk ((auxSizes d).L (auxSlot L W)) ((auxSizes d).W (auxSlot L W)) (auxEmb1 d L W a) = 0 := by
  unfold blk
  rw [auxEmb1_val, auxW_slot]
  have h1 := ZMod.val_lt a
  rw [Nat.div_eq_of_lt h1]
  simp

/-- The embedding of the fine lattice `Idx d L W = Z_{WL}^d` into the first block of the auxiliary
lattice, coordinatewise. -/
def auxEmb (d L W : ℕ) [NeZero L] [NeZero W] (i : Idx d L W) :
    Idx d ((auxSizes d).L (auxSlot L W)) ((auxSizes d).W (auxSlot L W)) :=
  fun k => auxEmb1 d L W (i k)

theorem auxEmb_injective (d L W : ℕ) [NeZero L] [NeZero W] :
    Function.Injective (auxEmb d L W) := by
  intro i j h
  funext k
  exact auxEmb1_injective d L W (congrFun h k)

/-- The image of the embedding lies in block `0` (each coordinate in block `0`). -/
theorem split_auxEmb_fst (d L W : ℕ) [NeZero L] [NeZero W] (i : Idx d L W) :
    (split d ((auxSizes d).L (auxSlot L W)) ((auxSizes d).W (auxSlot L W)) (auxEmb d L W i)).1
      = 0 := by
  funext k
  exact blk_auxEmb1 d L W (i k)

/-- The coordinate injection `ρ : CoordF d L W ↪ SeqCoord (auxSizes d)` of RBM1D `gueEntryRho`
(`GUEPhaseEntry.lean:133`), at one fixed size. -/
def auxRho (d L W : ℕ) [NeZero L] [NeZero W] (c : CoordF d L W) : (auxSizes d).SeqCoord :=
  ⟨auxSlot L W, (auxEmb d L W c.1, auxEmb d L W c.2.1, c.2.2)⟩

theorem auxRho_injective (d L W : ℕ) [NeZero L] [NeZero W] :
    Function.Injective (auxRho d L W) := by
  rintro ⟨i, j, b⟩ ⟨i', j', b'⟩ h
  have h2 := eq_of_heq (Sigma.mk.inj_iff.1 h).2
  simp only [Prod.mk.injEq] at h2
  obtain ⟨hi, hj, hb⟩ := h2
  rw [auxEmb_injective d L W hi, auxEmb_injective d L W hj, hb]

/-- **Positivity on one block, for every dimension and coupling** (the `d ≥ 3` replacement of the
`sbSupport 3` step of RBM2D `svar_aux_pos`, `AuxCarrier.lean:127`): two points of one block have
`svarF > 0`, since `sbKernelR d L g 0 = (1 + 2 d g²)⁻¹`. -/
theorem svarF_pos_of_block_eq (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (i j : Idx d L W)
    (h : (split d L W i).1 = (split d L W j).1) : 0 < svarF d L W g i j := by
  have h0 : sbKernelR d L g 0 = (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by
    simp [sbKernelR]
  have hW : (0 : ℝ) < W := Nat.cast_pos.2 (NeZero.pos W)
  have hk : (0 : ℝ) < (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ := by positivity
  unfold svarF SBR
  simp only [Matrix.of_apply]
  rw [h, sub_self, h0]
  positivity

/-- The auxiliary variance is positive on the image of the fine lattice (both points lie in block
`0`), at the auxiliary coupling `0`. -/
theorem svarF_aux_pos (d L W : ℕ) [NeZero L] [NeZero W] (i j : Idx d L W) :
    0 < svarF d ((auxSizes d).L (auxSlot L W)) ((auxSizes d).W (auxSlot L W)) 0
      (auxEmb d L W i) (auxEmb d L W j) :=
  svarF_pos_of_block_eq d _ _ 0 _ _
    ((split_auxEmb_fst d L W i).trans (split_auxEmb_fst d L W j).symm)

theorem seqGvar_aux_rho_pos (d L W : ℕ) [NeZero L] [NeZero W] (c : CoordF d L W) :
    0 < (Sizes.seqGvar (auxSizes d) (auxRho d L W c) : ℝ) := by
  have h := svarF_aux_pos d L W c.1 c.2.1
  change 0 < ((if auxEmb d L W c.1 = auxEmb d L W c.2.1 then
    svarF d ((auxSizes d).L (auxSlot L W)) ((auxSizes d).W (auxSlot L W)) 0
      (auxEmb d L W c.1) (auxEmb d L W c.2.1)
    else svarF d ((auxSizes d).L (auxSlot L W)) ((auxSizes d).W (auxSlot L W)) 0
      (auxEmb d L W c.1) (auxEmb d L W c.2.1) / 2 : ℝ))
  split_ifs <;> positivity

/-- Reindexing a product Gaussian measure along an injection (RBM1D
`gueEntry_infinitePi_map_comp`, `GUEPhaseEntry.lean:168`, verbatim). -/
theorem aux_infinitePi_map_comp {ι α : Type*} [Nonempty α] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {ρ : α → ι} (hρ : Function.Injective ρ) :
    (Measure.infinitePi μ).map (fun ω : ι → ℝ => fun a => ω (ρ a))
      = Measure.infinitePi (fun a => μ (ρ a)) := by
  classical
  have hmeas : Measurable (fun ω : ι → ℝ => fun a => ω (ρ a)) :=
    measurable_pi_iff.2 fun a => measurable_pi_apply (ρ a)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun a _ => ht a)]
  have hpre : (fun ω : ι → ℝ => fun a => ω (ρ a)) ⁻¹' ((s : Set α).pi t)
      = ((s.map ⟨ρ, hρ⟩ : Finset ι) : Set ι).pi (fun i => t (Function.invFun ρ i)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.coe_map,
      Function.Embedding.coeFn_mk, Set.mem_image]
    constructor
    · rintro h i ⟨a, ha, rfl⟩
      rw [Function.leftInverse_invFun hρ a]
      exact h a ha
    · intro h a ha
      have := h (ρ a) ⟨a, ha, rfl⟩
      rwa [Function.leftInverse_invFun hρ a] at this
  rw [hpre, Measure.infinitePi_pi _ (fun i _ => ht _), Finset.prod_map]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [Function.Embedding.coeFn_mk, Function.leftInverse_invFun hρ a]

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The scale turning the auxiliary coordinate `ρ c` into a coordinate of variance `v c`
(RBM1D `gueEntryScale`, `GUEPhaseEntry.lean:465`). -/
def auxScale (v : CoordF d L W → ℝ≥0) (c : CoordF d L W) : ℝ :=
  Real.sqrt ((v c : ℝ) / (Sizes.seqGvar (auxSizes d) (auxRho d L W c) : ℝ))

/-- The coordinate map `(T ω) c = s_c · ω (ρ c)` (RBM1D `gueEntryT`). -/
def auxT (v : CoordF d L W → ℝ≥0) (ω : Sizes.SeqΩ (auxSizes d)) : Ω d L W :=
  fun c => auxScale d L W v c * ω (auxRho d L W c)

theorem auxT_measurable (v : CoordF d L W → ℝ≥0) : Measurable (auxT d L W v) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).const_mul _

theorem continuous_auxT (v : CoordF d L W → ℝ≥0) : Continuous (auxT d L W v) :=
  continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem auxScale_sq (v : CoordF d L W → ℝ≥0) (c : CoordF d L W) :
    auxScale d L W v c ^ 2 * (Sizes.seqGvar (auxSizes d) (auxRho d L W c) : ℝ) = v c := by
  have hg := seqGvar_aux_rho_pos d L W c
  unfold auxScale
  rw [Real.sq_sqrt (div_nonneg (v c).coe_nonneg hg.le)]
  field_simp

/-- **Realisation of an arbitrary variance family** (RBM1D `gueEntry_map_T`,
`GUEPhaseEntry.lean:481`): the auxiliary Gaussian sample, rescaled coordinatewise, has the law of
independent centred Gaussians with the prescribed variances `v c` (zero allowed). -/
theorem auxT_law (v : CoordF d L W → ℝ≥0) :
    (Sizes.seqP (auxSizes d)).map (auxT d L W v)
      = Measure.infinitePi (fun c : CoordF d L W => gaussianReal 0 (v c)) := by
  have hre : auxT d L W v = (fun y : CoordF d L W → ℝ => fun c => auxScale d L W v c * y c) ∘
      (fun ω : Sizes.SeqΩ (auxSizes d) => fun c => ω (auxRho d L W c)) := rfl
  have hm1 : Measurable (fun ω : Sizes.SeqΩ (auxSizes d) => fun c => ω (auxRho d L W c)) :=
    measurable_pi_iff.2 fun c => measurable_pi_apply _
  have hm2 : ∀ c : CoordF d L W, Measurable (fun x : ℝ => auxScale d L W v c * x) :=
    fun c => measurable_const.mul measurable_id
  rw [hre, ← Measure.map_map (measurable_pi_iff.2 fun c => (measurable_pi_apply c).const_mul _)
    hm1, Sizes.seqP, aux_infinitePi_map_comp _ (auxRho_injective d L W)]
  refine (Measure.infinitePi_map_pi
    (μ := fun c : CoordF d L W => gaussianReal 0 (Sizes.seqGvar (auxSizes d) (auxRho d L W c)))
    (f := fun c (x : ℝ) => auxScale d L W v c * x) hm2).trans ?_
  refine congrArg Measure.infinitePi (funext fun c => ?_)
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  have h := auxScale_sq d L W v c
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  rw [← h]

/-- The auxiliary matrix `H = X(T ω)` on the auxiliary carrier (RBM1D `gueEntryHG`). -/
def auxHG (v : CoordF d L W → ℝ≥0) (ω : Sizes.SeqΩ (auxSizes d)) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  Xmat d L W (auxT d L W v ω)

/-- **The auxiliary matrix has the law of the Gaussian Hermitian matrix with coordinate variances
`v`** (RBM1D `gueEntry_law_HG`): the carrier is a *proof device*, no statement is moved. -/
theorem auxHG_law (v : CoordF d L W → ℝ≥0) :
    (Sizes.seqP (auxSizes d)).map (auxHG d L W v)
      = (Measure.infinitePi (fun c : CoordF d L W => gaussianReal 0 (v c))).map (Xmat d L W) := by
  have hXm : Measurable (Xmat d L W) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => measurable_Xentry d L W i j
  rw [← auxT_law d L W v, Measure.map_map hXm (auxT_measurable d L W v)]
  rfl

end Aux

/-- **Every variance family on one size is realised by a continuous map from a sequence carrier**
(the auxiliary carrier `auxSizes d` and `auxT`; RBM2D `auxT_law`, `AuxCarrier.lean:203`). -/
theorem exists_seqP_map_eq_gaussLaw (d L W : ℕ) [NeZero L] [NeZero W] (v : CoordF d L W → ℝ≥0) :
    ∃ (sz : Sizes d) (T : Sizes.SeqΩ sz → Ω d L W), Continuous T ∧
      (Sizes.seqP sz).map T = Measure.infinitePi (fun c : CoordF d L W => gaussianReal 0 (v c)) :=
  ⟨auxSizes d, auxT d L W v, continuous_auxT d L W v, auxT_law d L W v⟩

/-! ## §3 The variance families and profiles of the GUE phase and of the OU marginal -/

section Mix

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The law of independent centred Gaussian coordinates with variances `v`. -/
def gaussLaw (v : CoordF d L W → ℝ≥0) : Measure (Ω d L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (v c)

/-- `gueP` is `gaussLaw` of the GUE variances; `PF` is `gaussLaw` of the band variances. -/
theorem gueP_eq_gaussLaw : gueP d L W = gaussLaw d L W (gueVar d L W) := rfl

theorem PF_eq_gaussLaw (g : ℝ) : PF d L W g = gaussLaw d L W (gvarF d L W g) := rfl

/-- The coordinate variance family of `√a X_band(g) + √b X_GUE` (independent): `a gvarF g + b gueVar`.
It is the family of the GUE-phase grid path and, with `(a, b) = (e^{-t}, 1 - e^{-t})`, the merged
`ouVar` (`mixVar_exp_eq_ouVar`).  The coupling `g` is the profile coupling (`UNKind.lamV`). -/
def mixVar (g a b : ℝ) (c : CoordF d L W) : ℝ≥0 :=
  a.toNNReal * gvarF d L W g c + b.toNNReal * gueVar d L W c

/-- The entry-variance profile `S_{ij} = a S^{band}_{ij}(g) + b N⁻¹` of `mixVar g a b`,
`N = (W L)^d` (`ζ = b / (a + b)`: `(a + b) · S̃`). -/
def Smix (g a b : ℝ) (i j : Idx d L W) : ℝ :=
  a * svarF d L W g i j + b / (((W * L) ^ d : ℕ) : ℝ)

theorem mixVar_exp_eq_ouVar (g t : ℝ) (c : CoordF d L W) :
    mixVar d L W g (Real.exp (-t)) (1 - Real.exp (-t)) c = ouVar d L W g t c := rfl

theorem Smix_symm (g a b : ℝ) (i j : Idx d L W) :
    Smix d L W g a b i j = Smix d L W g a b j i := by
  simp [Smix, svarF_comm d L W g i j]

theorem Smix_nonneg {a b : ℝ} (g : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (i j : Idx d L W) :
    0 ≤ Smix d L W g a b i j := by
  unfold Smix
  have := svarF_nonneg d L W g i j
  positivity

/-- Row sums: `∑_j Smix g a b i j = a + b` (`S1 = 1` by `IBP_sum_svarF_row`, `N · N⁻¹ = 1`). -/
theorem sum_Smix_row (hL : 3 ≤ L) (g a b : ℝ) (i : Idx d L W) :
    ∑ j : Idx d L W, (a * svarF d L W g i j + b / (((W * L) ^ d : ℕ) : ℝ)) = a + b := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Green.IBP_sum_svarF_row g hL, Finset.sum_const,
    Finset.card_univ, RBM.Gauss.card_Idx, nsmul_eq_mul]
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  field_simp

theorem sum_Smix_col (hL : 3 ≤ L) (g a b : ℝ) (j : Idx d L W) :
    ∑ i : Idx d L W, Smix d L W g a b i j = a + b := by
  simp_rw [Smix_symm d L W g a b _ j]
  exact sum_Smix_row d L W hL g a b j

theorem mixVar_zero_right (g a : ℝ) (c : CoordF d L W) :
    mixVar d L W g a 0 c = a.toNNReal * gvarF d L W g c := by
  simp [mixVar]

theorem mixVar_zero_left (g b : ℝ) (c : CoordF d L W) :
    mixVar d L W g 0 b c = b.toNNReal * gueVar d L W c := by
  simp [mixVar]

/-- Tag-free variance family: the real and imaginary coordinates of an entry have the same
variance (true for `mixVar`, `gvarF` and `gueVar`). -/
def TagFree (v : CoordF d L W → ℝ≥0) : Prop := ∀ i j : Idx d L W, v (i, j, true) = v (i, j, false)

theorem gueVar_tagFree : TagFree d L W (gueVar d L W) := fun _ _ => rfl

theorem gvarF_tagFree (g : ℝ) : TagFree d L W (gvarF d L W g) := fun _ _ => rfl

/-- The mixture family is tag-free (RBM2D `EntryTail.lean:279`, moved here). -/
theorem mixVar_tagFree (g a b : ℝ) : TagFree d L W (mixVar d L W g a b) := fun _ _ => rfl

end Mix

/-! ## §6b The Hanson–Wright tail for an arbitrary row chaos (generic wrapper of the merged moment bound) -/

section GenericTail

open RBM.Green

variable {d : ℕ} {sz : Sizes d} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem RowChaos_continuous_Vq (C : RowChaos sz κ) : Continuous C.Vq := by
  unfold RowChaos.Vq
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact (continuous_const.mul ((C.B_cont k l).norm.pow 2)).mul continuous_const

theorem RowChaos_Vq_congr (C : RowChaos sz κ) {ω ω' : Sizes.SeqΩ sz}
    (h : ∀ c ∈ C.Ifree, ω c = ω' c) : C.Vq ω = C.Vq ω' := by
  unfold RowChaos.Vq
  rw [C.B_free ω ω' h]

/-- **The `ε`-normalised row chaos, for an arbitrary row chaos** (generic version of the merged
`modelChaosEps`): the matrix divided by `(V_q + ε)^{1/2}`. -/
def chaosEps (C : RowChaos sz κ) (ε : ℝ) (hε : 0 < ε) : RowChaos sz κ :=
  { C with
    B := fun ω k l => C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    B_cont := fun k l => by
      refine (C.B_cont k l).div ?_ ?_
      · exact Complex.continuous_ofReal.comp ((RowChaos_continuous_Vq C).add continuous_const).sqrt
      · intro ω
        have : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
        exact_mod_cast this.ne'
    Bbd := C.Bbd / Real.sqrt ε
    B_bdd := fun ω k l => by
      have hpos : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
      have hge : Real.sqrt ε ≤ Real.sqrt (C.Vq ω + ε) :=
        Real.sqrt_le_sqrt (by linarith [C.Vq_nonneg ω])
      have hεp : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]
      exact div_le_div₀ (by
        have := C.B_bdd ω k l
        have h0 : 0 ≤ ‖C.B ω k l‖ := norm_nonneg _
        linarith) (C.B_bdd ω k l) hεp hge
    B_free := fun ω ω' h => by
      have hs : Real.sqrt (C.Vq ω + ε) = Real.sqrt (C.Vq ω' + ε) := by
        rw [RowChaos_Vq_congr C h]
      funext k l
      rw [C.B_free ω ω' h, hs] }

theorem chaosEps_chaos (C : RowChaos sz κ) {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ sz) :
    (chaosEps C ε hε).chaos ω = C.chaos ω / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ) := by
  unfold RowChaos.chaos RowChaos.cen
  rw [sub_div]
  congr 1
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    change C.h ω k * (C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)) * (starRingEnd ℂ) (C.h ω l)
      = C.h ω k * C.B ω k l * (starRingEnd ℂ) (C.h ω l) / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    ring
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    change ((C.sg k : ℝ) : ℂ) * (C.B ω k k / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ))
      = ((C.sg k : ℝ) : ℂ) * C.B ω k k / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)
    ring

theorem chaosEps_Vq (C : RowChaos sz κ) {ε : ℝ} (hε : 0 < ε) (ω : Sizes.SeqΩ sz) :
    (chaosEps C ε hε).Vq ω = C.Vq ω / (C.Vq ω + ε) := by
  have hpos : 0 < Real.sqrt (C.Vq ω + ε) := Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
  have hsq : Real.sqrt (C.Vq ω + ε) ^ 2 = C.Vq ω + ε :=
    Real.sq_sqrt (by linarith [C.Vq_nonneg ω])
  have hpt : ∀ k l : κ, (chaosEps C ε hε).sg k * ‖(chaosEps C ε hε).B ω k l‖ ^ 2 *
        (chaosEps C ε hε).sg l = (C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) / (C.Vq ω + ε) := by
    intro k l
    change C.sg k * ‖C.B ω k l / ((Real.sqrt (C.Vq ω + ε) : ℝ) : ℂ)‖ ^ 2 * C.sg l = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le, div_pow, hsq]
    ring
  have hd : ∀ (A : κ → κ → ℝ) (c : ℝ), (∑ k, ∑ l, A k l / c) = (∑ k, ∑ l, A k l) / c := by
    intro A c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (Finset.sum_div _ _ _).symm
  unfold RowChaos.Vq
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l,
    hd (fun k l => C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) (C.Vq ω + ε)]
  rfl

theorem chaosEps_Vq_le_one (C : RowChaos sz κ) {ε : ℝ} (hε : 0 < ε)
    (ω : Sizes.SeqΩ sz) : (chaosEps C ε hε).Vq ω ≤ 1 := by
  rw [chaosEps_Vq C hε ω]
  have h0 := C.Vq_nonneg ω
  rw [div_le_one (by linarith)]
  linarith

/-- **`E[(|Q|²/(V_q+ε))^{q+1}] ≤ A_{q+1}` for an arbitrary row chaos**, uniformly in `ε`. -/
theorem chaosEps_mom_le (C : RowChaos sz κ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    (chaosEps C ε hε).mom (q + 1) ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) := by
  have h := (chaosEps C ε hε).mom_le_momVpow (gaussIBP sz) q
  have hV : (chaosEps C ε hε).momVpow (q + 1) ≤ 1 := by
    change (∫ ω, (chaosEps C ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP sz)) ≤ 1
    calc ∫ ω, (chaosEps C ε hε).Vq ω ^ (q + 1) ∂(Sizes.seqP sz)
        ≤ ∫ _ω : Sizes.SeqΩ sz, (1 : ℝ) ∂(Sizes.seqP sz) :=
          MeasureTheory.integral_mono
            ((chaosEps C ε hε).integrable_Vq_pow (gaussIBP sz) (q + 1))
            (MeasureTheory.integrable_const 1)
            (fun ω => pow_le_one₀ (RowChaos.Vq_nonneg ω) (chaosEps_Vq_le_one C hε ω))
      _ = 1 := by simp
  have hc : (0 : ℝ) ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) := by positivity
  refine h.trans ?_
  calc ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * (chaosEps C ε hε).momVpow (q + 1)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * 1 :=
        mul_le_mul_of_nonneg_left hV hc
    _ = _ := mul_one _

/-- **Markov at fixed `ε`** for an arbitrary row chaos. -/
theorem chaos_tail_eps (C : RowChaos sz κ) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    (Sizes.seqP sz) {ω | lam * (C.Vq ω + ε) < ‖C.chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set C' := chaosEps C ε hε with hC'
  set Y : Sizes.SeqΩ sz → ℝ := fun ω => ‖C'.chaos ω‖ with hY
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => norm_nonneg _
  have habs : ∀ ω, |Y ω| ^ (2 * (q + 1)) = ‖C'.chaos ω‖ ^ (2 * (q + 1)) := fun ω => by
    rw [hY, abs_of_nonneg (hYnn ω)]
  have hint : Integrable (fun ω => |Y ω| ^ (2 * (q + 1))) (Sizes.seqP sz) := by
    simpa only [habs] using C'.integrable_norm_pow (gaussIBP sz) (q + 1)
  have hmom0 : (∫ ω, ‖C'.chaos ω‖ ^ (2 * (q + 1)) ∂(Sizes.seqP sz)) ≤ hwConst q :=
    chaosEps_mom_le C hε q
  have hmom : ∫ ω, |Y ω| ^ (2 * (q + 1)) ∂(Sizes.seqP sz) ≤ hwConst q := by
    simpa only [habs] using hmom0
  have ht : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hmark := meas_gt_le_of_moment (P := Sizes.seqP sz) (Y := Y) ht hint hmom
  have hset : {ω | lam * (C.Vq ω + ε) < ‖C.chaos ω‖ ^ 2} = {ω | Real.sqrt lam < Y ω} := by
    ext ω
    obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt (C.Vq ω + ε) := ⟨_, rfl⟩
    have hs : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 (by linarith [C.Vq_nonneg ω])
    have hsq : s ^ 2 = C.Vq ω + ε := by
      rw [hsdef]; exact Real.sq_sqrt (by linarith [C.Vq_nonneg ω])
    have hYv : Y ω = ‖C.chaos ω‖ / s := by
      change ‖C'.chaos ω‖ = _
      rw [hC', chaosEps_chaos C hε ω, norm_div, Complex.norm_real, Real.norm_eq_abs, ← hsdef,
        abs_of_nonneg hs.le]
    have hc : (0 : ℝ) ≤ ‖C.chaos ω‖ := norm_nonneg _
    have hsl : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam.le
    have hsln : (0 : ℝ) ≤ Real.sqrt lam := Real.sqrt_nonneg lam
    simp only [Set.mem_ofPred_eq, hYv]
    rw [lt_div_iff₀ hs, ← hsq]
    constructor
    · intro h
      nlinarith [h, hs, hc, hsl, hsln, sq_nonneg (Real.sqrt lam * s - ‖C.chaos ω‖),
        sq_nonneg (Real.sqrt lam * s + ‖C.chaos ω‖)]
    · intro h
      have hms := mul_self_lt_mul_self (mul_nonneg hsln hs.le) h
      nlinarith [hms, hsl, hs]
  rw [hset]
  refine hmark.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : Real.sqrt lam ^ (2 * (q + 1)) = lam ^ (q + 1) := by
    rw [pow_mul, Real.sq_sqrt hlam.le]
  rw [hpow]

/-- **Hanson–Wright tail for an arbitrary row chaos with its random control**:
`P(λ V_q < |Q|²) ≤ A_q / λ^{q+1}`, the `ε → 0` limit of `chaos_tail_eps` by continuity of the
measure from below.  Generic: this is what the merged `meas_lt_normSq_chaos_le` proves for the
band instance `modelChaos` only. -/
theorem chaos_tail (C : RowChaos sz κ) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    (Sizes.seqP sz) {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  set S : ℕ → Set (Sizes.SeqΩ sz) := fun m =>
    {ω | lam * (C.Vq ω + 1 / ((m : ℝ) + 1)) < ‖C.chaos ω‖ ^ 2} with hS
  have hmono : Monotone S := by
    intro m m' hmm ω hω
    simp only [hS, Set.mem_ofPred_eq] at hω ⊢
    have h1 : (1 : ℝ) / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := by
      have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hmm' : ((m : ℝ) + 1) ≤ ((m' : ℝ) + 1) := by
        have : (m : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hmm
        linarith
      exact one_div_le_one_div_of_le hm hmm'
    nlinarith [hω, h1, hlam]
  have hunion : (⋃ m, S m) = {ω | lam * C.Vq ω < ‖C.chaos ω‖ ^ 2} := by
    ext ω
    simp only [Set.mem_iUnion, hS, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      nlinarith [hm, hlam, hpos]
    · intro h
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt
        (show (0 : ℝ) < (‖C.chaos ω‖ ^ 2 - lam * C.Vq ω) / lam by
          apply div_pos _ hlam; linarith)
      refine ⟨m, ?_⟩
      rw [lt_div_iff₀ hlam] at hm
      nlinarith [hm]
  rw [← hunion]
  refine le_of_tendsto (tendsto_measure_iUnion_atTop (μ := Sizes.seqP sz) hmono)
    (Filter.Eventually.of_forall fun m => ?_)
  exact chaos_tail_eps C hlam q (by positivity)

end GenericTail

/-! ## §6c The row chaos on the auxiliary carrier, with a deterministic Hermitian shift

The Gaussian row `(H_{ik})_{k ≠ i}` of the rescaled auxiliary matrix `auxHG v ω` is
`H_{ik} = λ_{ik} (ω_{ρ c_re} + ε_{ik} i ω_{ρ c_im})`: a `RowChaos (auxSizes d)` with `r = 1` and the
matrix `B_{kl} = λ_k G^{(i)}(A + X)_{kl} λ_l` (the scales `λ_{ik} = s_c` of §2 are absorbed into `B`),
so that the merged moment bound applies to the quadratic form of (4.7) *for any variance family `v`*
and for the minor of `A + X` with `A` a deterministic Hermitian matrix: the minor reads no
coordinate of row `i`, and `A` reads none.  This is the point of the shift (DECISIONS §57 (2)): the
mean `μ` of a centred model enters the Schur complement of `μ + X`. -/

section AuxRowChaos

open RBM.Green

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The coordinate carrying the real (`true`) or imaginary (`false`) part of `X_{ik}`. -/
def rowCoordF (i k : Idx d L W) (b : Bool) : CoordF d L W :=
  if idxKey d L W i < idxKey d L W k then (i, k, b) else (k, i, b)

/-- The sign with which the imaginary coordinate enters `X_{ik}`. -/
def rowSignF (i k : Idx d L W) : ℝ := if idxKey d L W i < idxKey d L W k then 1 else -1

private theorem auxCarrier_Xmat_apply (ω : Ω d L W) (i j : Idx d L W) :
    Xmat d L W ω i j = Xentry d L W ω i j := rfl

theorem Xentry_eq_rowCoordF {i k : Idx d L W} (hik : i ≠ k) (s : Ω d L W) :
    Xentry d L W s i k = (s (rowCoordF d L W i k true) : ℂ)
      + (rowSignF d L W i k : ℂ) * Complex.I * (s (rowCoordF d L W i k false) : ℂ) := by
  have hkey : idxKey d L W i ≠ idxKey d L W k := fun h => hik (idxKey_injective d L W h)
  unfold Xentry rowCoordF rowSignF
  rcases lt_or_gt_of_ne hkey with h | h
  · simp only [h, ↓reduceIte]
    push_cast
    ring
  · have h' : ¬ idxKey d L W i < idxKey d L W k := by omega
    simp only [h', ↓reduceIte, h]
    push_cast
    ring

theorem rowCoordF_injOn {i k l : Idx d L W} {b c : Bool} (hk : k ≠ i) (hl : l ≠ i)
    (h : rowCoordF d L W i k b = rowCoordF d L W i l c) : k = l ∧ b = c := by
  unfold rowCoordF at h
  split_ifs at h with h1 h2 h2 <;> simp only [Prod.mk.injEq] at h
  · exact ⟨h.2.1, h.2.2⟩
  · exact absurd h.1.symm hl
  · exact absurd h.1 hk
  · exact ⟨h.1, h.2.2⟩

theorem seqGvar_auxRho_tag (i j : Idx d L W) :
    Sizes.seqGvar (auxSizes d) (auxRho d L W (i, j, true))
      = Sizes.seqGvar (auxSizes d) (auxRho d L W (i, j, false)) := rfl

theorem auxScale_tag {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v) (i j : Idx d L W) :
    auxScale d L W v (i, j, false) = auxScale d L W v (i, j, true) := by
  unfold auxScale
  rw [seqGvar_auxRho_tag, hv i j]

/-- **The entry `H_{ik}` of the auxiliary matrix** in terms of the two row coordinates of the
auxiliary carrier: `λ_{ik} (ω_{ρ c_re} + ε i ω_{ρ c_im})`. -/
theorem auxHG_apply {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v) {i k : Idx d L W} (hik : i ≠ k)
    (ω : Sizes.SeqΩ (auxSizes d)) :
    auxHG d L W v ω i k = (auxScale d L W v (rowCoordF d L W i k true) : ℂ) *
      ((ω (auxRho d L W (rowCoordF d L W i k true)) : ℂ) + (rowSignF d L W i k : ℂ) * Complex.I *
        (ω (auxRho d L W (rowCoordF d L W i k false)) : ℂ)) := by
  unfold auxHG
  rw [auxCarrier_Xmat_apply, Xentry_eq_rowCoordF d L W hik]
  have h : auxScale d L W v (rowCoordF d L W i k false)
      = auxScale d L W v (rowCoordF d L W i k true) := by
    unfold rowCoordF; split_ifs <;> exact auxScale_tag d L W hv _ _
  simp only [auxT, h]
  push_cast
  ring

/-- The `i`-th row scale `λ_{ik}` of the auxiliary matrix. -/
def lamRow (v : CoordF d L W → ℝ≥0) (i k : Idx d L W) : ℝ :=
  auxScale d L W v (rowCoordF d L W i k true)

theorem lamRow_nonneg (v : CoordF d L W → ℝ≥0) (i k : Idx d L W) : 0 ≤ lamRow d L W v i k :=
  Real.sqrt_nonneg _

theorem continuous_auxHG (v : CoordF d L W → ℝ≥0) : Continuous (auxHG d L W v) :=
  (continuous_Xmat d L W).comp (continuous_auxT d L W v)

theorem auxHG_isHermitian (v : CoordF d L W → ℝ≥0) (ω : Sizes.SeqΩ (auxSizes d)) :
    (auxHG d L W v ω).IsHermitian :=
  Xmat_isHermitian d L W _

section MinorBounds

open scoped Matrix.Norms.L2Operator

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`
(through `RBM.Ind.Gres_eq_green_zSig`). -/
private theorem auxCarrier_Gres_true {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (z : ℂ) : Gres H z true = green H z := by
  rw [RBM.Ind.Gres_eq_green_zSig]
  rfl

/-- An entry of the resolvent of a Hermitian matrix is at most `|Im z|⁻¹` (merged
`norm_Gsig_le_inv_eta` and `norm_apply_le_l2_opNorm`; the private
`LDEQuadInst_norm_green_apply_le` of `Green/IBPPoly.lean:412` is the pattern). -/
private theorem auxCarrier_norm_green_apply_le {ν : Type*} [Fintype ν] [DecidableEq ν]
    {H : Matrix ν ν ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (p q : ν) :
    ‖green H z p q‖ ≤ |z.im|⁻¹ := by
  have h := norm_Gsig_le_inv_eta hH (abs_pos.2 hz) le_rfl true
  rw [auxCarrier_Gres_true] at h
  exact (RBM.Ind.norm_apply_le_l2_opNorm _ p q).trans h

end MinorBounds

/-- The minor resolvent `((A + H)^{(i)} - z)⁻¹` of the auxiliary matrix shifted by the deterministic
matrix `A`. -/
def auxMinorRes (v : CoordF d L W → ℝ≥0) (A : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d)) :
    Matrix {a : Idx d L W // a ≠ i} {a : Idx d L W // a ≠ i} ℂ :=
  green ((A + auxHG d L W v ω).submatrix Subtype.val Subtype.val) z

theorem norm_auxMinorRes_le (v : CoordF d L W → ℝ≥0) {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d))
    (k l : {a : Idx d L W // a ≠ i}) :
    ‖auxMinorRes d L W v A z i ω k l‖ ≤ |z.im|⁻¹ :=
  auxCarrier_norm_green_apply_le ((hA.add (auxHG_isHermitian d L W v ω)).submatrix _) hz k l

theorem continuous_auxMinorRes (v : CoordF d L W → ℝ≥0) {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W)
    (k l : {a : Idx d L W // a ≠ i}) :
    Continuous fun ω => auxMinorRes d L W v A z i ω k l := by
  have h := RBM.Gauss.continuous_green_of_isHermitian
    (f := fun ω : Sizes.SeqΩ (auxSizes d) => (A + auxHG d L W v ω).submatrix Subtype.val Subtype.val)
    ((continuous_const.add (continuous_auxHG d L W v)).matrix_submatrix
      (Subtype.val : {a : Idx d L W // a ≠ i} → Idx d L W)
      (Subtype.val : {a : Idx d L W // a ≠ i} → Idx d L W))
    (fun ω => (hA.add (auxHG_isHermitian d L W v ω)).submatrix _) hz
  simp only [auxCarrier_Gres_true] at h
  exact h.matrix_elem k l

open Classical in
/-- The coordinates of the auxiliary carrier that the minor `(A + H)^{(i)}` can read. -/
def auxOffRow (i : Idx d L W) : Finset (Sizes.SeqCoord (auxSizes d)) :=
  ((Finset.univ : Finset (CoordF d L W)).filter (fun c => c.1 ≠ i ∧ c.2.1 ≠ i)).image
    (auxRho d L W)

theorem Xentry_congr_offRow {i k l : Idx d L W} (hk : k ≠ i) (hl : l ≠ i) {s s' : Ω d L W}
    (h : ∀ c : CoordF d L W, c.1 ≠ i → c.2.1 ≠ i → s c = s' c) :
    Xentry d L W s k l = Xentry d L W s' k l := by
  unfold Xentry
  split_ifs
  · simp [h (k, l, true) hk hl, h (k, l, false) hk hl]
  · simp [h (l, k, true) hl hk, h (l, k, false) hl hk]
  · simp [h (k, l, true) hk hl]

/-- **The shifted minor reads only off-row coordinates**: `A` reads none. -/
theorem auxMinorRes_congr (v : CoordF d L W → ℝ≥0) (A : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (i : Idx d L W)
    {ω ω' : Sizes.SeqΩ (auxSizes d)} (h : ∀ c ∈ auxOffRow d L W i, ω c = ω' c) :
    auxMinorRes d L W v A z i ω = auxMinorRes d L W v A z i ω' := by
  unfold auxMinorRes
  congr 1
  ext k l
  simp only [Matrix.submatrix_apply, Matrix.add_apply, auxHG, auxCarrier_Xmat_apply]
  congr 1
  apply Xentry_congr_offRow d L W k.2 l.2
  intro c hc1 hc2
  simp only [auxT]
  have hmem : auxRho d L W c ∈ auxOffRow d L W i := by
    classical
    unfold auxOffRow
    exact Finset.mem_image.2 ⟨c, by simp [hc1, hc2], rfl⟩
  rw [h _ hmem]

/-- **The quadratic row chaos of the shifted auxiliary matrix `A + H` at row `i`** (the `d`-dimensional
counterpart of RBM1D `gueEntryQuadChaos`, `Flow/GUEPhaseEntry.lean:1469`, with the shift `A`):
coordinates `ρ (rowCoordF i k b)`, signs `rowSignF`, scale `r = 1`, matrix
`B_{kl} = λ_k G^{(i)}(A + H)_{kl} λ_l` (continuous, bounded, off-row). -/
noncomputable def auxQuadChaos (v : CoordF d L W → ℝ≥0)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) : RowChaos (auxSizes d) {a : Idx d L W // a ≠ i} where
  co k b := auxRho d L W (rowCoordF d L W i k.1 b)
  co_inj := by
    rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
    obtain ⟨h1, h2⟩ := rowCoordF_injOn d L W hk hl (auxRho_injective d L W h)
    subst h1; subst h2; rfl
  gvar_tag k := by
    unfold rowCoordF
    split_ifs <;> exact_mod_cast (seqGvar_auxRho_tag d L W _ _).symm
  eps k := rowSignF d L W i k.1
  eps_sq k := by unfold rowSignF; split_ifs <;> norm_num
  r := 1
  B ω k l := (lamRow d L W v i k.1 : ℂ) * auxMinorRes d L W v A z i ω k l *
    (lamRow d L W v i l.1 : ℂ)
  B_cont k l :=
    (continuous_const.mul (continuous_auxMinorRes d L W v hA hz i k l)).mul continuous_const
  Bbd := (∑ k : {a : Idx d L W // a ≠ i}, lamRow d L W v i k.1) ^ 2 * |z.im|⁻¹
  B_bdd ω k l := by
    have hk : lamRow d L W v i k.1 ≤ ∑ j : {a : Idx d L W // a ≠ i}, lamRow d L W v i j.1 :=
      Finset.single_le_sum (f := fun j : {a : Idx d L W // a ≠ i} => lamRow d L W v i j.1)
        (fun j _ => lamRow_nonneg d L W v i j.1) (Finset.mem_univ k)
    have hl : lamRow d L W v i l.1 ≤ ∑ j : {a : Idx d L W // a ≠ i}, lamRow d L W v i j.1 :=
      Finset.single_le_sum (f := fun j : {a : Idx d L W // a ≠ i} => lamRow d L W v i j.1)
        (fun j _ => lamRow_nonneg d L W v i j.1) (Finset.mem_univ l)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (lamRow_nonneg d L W v i k.1),
      abs_of_nonneg (lamRow_nonneg d L W v i l.1)]
    have hG := norm_auxMinorRes_le d L W v hA hz i ω k l
    have h0 := lamRow_nonneg d L W v i k.1
    have h1 := lamRow_nonneg d L W v i l.1
    calc lamRow d L W v i k.1 * ‖auxMinorRes d L W v A z i ω k l‖ * lamRow d L W v i l.1
        ≤ (∑ j : {a : Idx d L W // a ≠ i}, lamRow d L W v i j.1) * |z.im|⁻¹ *
          (∑ j : {a : Idx d L W // a ≠ i}, lamRow d L W v i j.1) := by
          apply mul_le_mul _ hl h1
            (mul_nonneg (Finset.sum_nonneg fun j _ => lamRow_nonneg d L W v i j.1) (by positivity))
          exact mul_le_mul hk hG (norm_nonneg _) (h0.trans hk)
      _ = _ := by ring
  Ifree := auxOffRow d L W i
  Ifree_free k b := by
    classical
    unfold auxOffRow
    intro hmem
    obtain ⟨c, hc, hc'⟩ := Finset.mem_image.1 hmem
    have hc2 : c = rowCoordF d L W i k.1 b := auxRho_injective d L W hc'
    have hc3 := (Finset.mem_filter.1 hc).2
    rw [hc2] at hc3
    unfold rowCoordF at hc3
    split_ifs at hc3 with h
    · exact hc3.1 rfl
    · exact hc3.2 rfl
  B_free ω ω' h := by
    funext k l
    rw [auxMinorRes_congr d L W v A z i h]

/-- The variance `E|H_{ik}|² = 2 v_{(i,k)}` of the entry `(i, k)` (two real coordinates). -/
def sigRow (v : CoordF d L W → ℝ≥0) (i k : Idx d L W) : ℝ :=
  2 * (v (rowCoordF d L W i k true) : ℝ)

/-- The Hanson–Wright proxy `∑_{k,l} σ_{ik} |G^{(i)}_{kl}|² σ_{il}` of the minor of `A + Xmat s`. -/
def quadVqS (v : CoordF d L W → ℝ≥0) (A : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (i : Idx d L W) (s : Ω d L W) : ℝ :=
  ∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
    sigRow d L W v i k.1 *
      ‖green ((A + Xmat d L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2 *
      sigRow d L W v i l.1

/-- The centred quadratic form of (4.7) of `A + Xmat s` at row `i`:
`∑_{k,l ≠ i} X_{ik} G^{(i)}_{kl} X_{li} - ∑_{k ≠ i} σ_{ik} G^{(i)}_{kk}` (the row entries are those of
the centred `X`; `G^{(i)}` is the minor resolvent of `A + X`). -/
def quadQS (v : CoordF d L W → ℝ≥0) (A : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (i : Idx d L W) (s : Ω d L W) : ℂ :=
  (∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
      Xmat d L W s i k.1 * green ((A + Xmat d L W s).submatrix Subtype.val Subtype.val) z k l *
        Xmat d L W s l.1 i)
    - ∑ k : {a : Idx d L W // a ≠ i}, (sigRow d L W v i k.1 : ℂ) *
        green ((A + Xmat d L W s).submatrix Subtype.val Subtype.val) z k k

variable {d L W}

theorem auxQuadChaos_sg {v : CoordF d L W → ℝ≥0} {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W)
    (k : {a : Idx d L W // a ≠ i}) :
    (auxQuadChaos d L W v hA hz i).sg k * lamRow d L W v i k.1 ^ 2 = sigRow d L W v i k.1 := by
  have h := auxScale_sq d L W v (rowCoordF d L W i k.1 true)
  change 2 * (1 : ℝ) ^ 2 *
      (Sizes.seqGvar (auxSizes d) (auxRho d L W (rowCoordF d L W i k.1 true)) : ℝ) *
      auxScale d L W v (rowCoordF d L W i k.1 true) ^ 2 = 2 * (v (rowCoordF d L W i k.1 true) : ℝ)
  rw [← h]
  ring

/-- **The row of the chaos is the `i`-th row of the auxiliary matrix**, up to the scale `λ_{ik}`. -/
theorem auxQuadChaos_h {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d)) (k : {a : Idx d L W // a ≠ i}) :
    auxHG d L W v ω i k.1 = (lamRow d L W v i k.1 : ℂ) * (auxQuadChaos d L W v hA hz i).h ω k := by
  rw [auxHG_apply d L W hv (Ne.symm k.2)]
  change _ = (lamRow d L W v i k.1 : ℂ) * (((1 : ℝ) : ℂ) *
    ((ω (auxRho d L W (rowCoordF d L W i k.1 true)) : ℂ) +
      ((rowSignF d L W i k.1 : ℝ) : ℂ) * Complex.I *
      (ω (auxRho d L W (rowCoordF d L W i k.1 false)) : ℂ)))
  unfold lamRow
  push_cast
  ring

theorem auxHG_swap (v : CoordF d L W → ℝ≥0) (ω : Sizes.SeqΩ (auxSizes d)) (k l : Idx d L W) :
    auxHG d L W v ω l k = (starRingEnd ℂ) (auxHG d L W v ω k l) :=
  Xentry_swap d L W _ k l

/-- **The chaos is the quadratic form of (4.7), centred**: for the shifted auxiliary matrix `A + H`,
`Q_i - ∑_k E|H_{ik}|² G^{(i)}_{kk}` with `Q_i = ∑_{k,l ≠ i} H_{ik} G^{(i)}(A + H)_{kl} H_{li}`. -/
theorem auxQuadChaos_chaos {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d)) :
    (auxQuadChaos d L W v hA hz i).chaos ω =
      (∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
          auxHG d L W v ω i k.1 * auxMinorRes d L W v A z i ω k l * auxHG d L W v ω l.1 i)
        - ∑ k : {a : Idx d L W // a ≠ i},
          (sigRow d L W v i k.1 : ℂ) * auxMinorRes d L W v A z i ω k k := by
  unfold RowChaos.chaos RowChaos.cen
  congr 1
  · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [auxQuadChaos_h hv hA hz i ω k, auxHG_swap, auxQuadChaos_h hv hA hz i ω l]
    simp only [map_mul, Complex.conj_ofReal]
    change (auxQuadChaos d L W v hA hz i).h ω k *
        ((lamRow d L W v i k.1 : ℂ) * auxMinorRes d L W v A z i ω k l *
          (lamRow d L W v i l.1 : ℂ)) *
        (starRingEnd ℂ) ((auxQuadChaos d L W v hA hz i).h ω l) = _
    ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hs := auxQuadChaos_sg (v := v) hA hz i k
    change (((auxQuadChaos d L W v hA hz i).sg k : ℝ) : ℂ) *
        ((lamRow d L W v i k.1 : ℂ) * auxMinorRes d L W v A z i ω k k *
          (lamRow d L W v i k.1 : ℂ)) = _
    rw [← hs]
    push_cast
    ring

/-- **The control of the chaos is the Hanson–Wright proxy** `∑_{k,l} σ_{ik} |G^{(i)}_{kl}|² σ_{il}`. -/
theorem auxQuadChaos_Vq {v : CoordF d L W → ℝ≥0} {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d)) :
    (auxQuadChaos d L W v hA hz i).Vq ω =
      ∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
        sigRow d L W v i k.1 * ‖auxMinorRes d L W v A z i ω k l‖ ^ 2 * sigRow d L W v i l.1 := by
  unfold RowChaos.Vq
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hk := auxQuadChaos_sg (v := v) hA hz i k
  have hl := auxQuadChaos_sg (v := v) hA hz i l
  change (auxQuadChaos d L W v hA hz i).sg k *
      ‖(lamRow d L W v i k.1 : ℂ) * auxMinorRes d L W v A z i ω k l *
        (lamRow d L W v i l.1 : ℂ)‖ ^ 2 *
      (auxQuadChaos d L W v hA hz i).sg l = _
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (lamRow_nonneg d L W v i k.1), abs_of_nonneg (lamRow_nonneg d L W v i l.1),
    ← hk, ← hl]
  ring

theorem continuous_green_minorS {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) (k l : {a : Idx d L W // a ≠ i}) :
    Continuous fun s : Ω d L W =>
      green ((A + Xmat d L W s).submatrix Subtype.val Subtype.val) z k l := by
  have h := RBM.Gauss.continuous_green_of_isHermitian
    (f := fun s : Ω d L W => (A + Xmat d L W s).submatrix Subtype.val Subtype.val)
    ((continuous_const.add (continuous_Xmat d L W)).matrix_submatrix
      (Subtype.val : {a : Idx d L W // a ≠ i} → Idx d L W)
      (Subtype.val : {a : Idx d L W // a ≠ i} → Idx d L W))
    (fun s => (hA.add (Xmat_isHermitian d L W s)).submatrix _) hz
  simp only [auxCarrier_Gres_true] at h
  exact h.matrix_elem k l

theorem continuous_Xmat_apply (i j : Idx d L W) : Continuous fun s : Ω d L W => Xmat d L W s i j :=
  (continuous_Xmat d L W).matrix_elem i j

theorem continuous_quadVqS (v : CoordF d L W → ℝ≥0) {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) :
    Continuous (quadVqS d L W v A z i) := by
  unfold quadVqS
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  exact (continuous_const.mul ((continuous_green_minorS hA hz i k l).norm.pow 2)).mul
    continuous_const

theorem continuous_quadQS (v : CoordF d L W → ℝ≥0) {A : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) :
    Continuous (quadQS d L W v A z i) := by
  unfold quadQS
  refine Continuous.sub ?_ ?_
  · refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
    exact ((continuous_Xmat_apply i k.1).mul (continuous_green_minorS hA hz i k l)).mul
      (continuous_Xmat_apply l.1 i)
  · exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_green_minorS hA hz i k k)

/-- The chaos and its control are the functions `quadQS`, `quadVqS` of the rescaled sample. -/
theorem auxQuadChaos_eq {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d)) :
    (auxQuadChaos d L W v hA hz i).chaos ω = quadQS d L W v A z i (auxT d L W v ω) ∧
      (auxQuadChaos d L W v hA hz i).Vq ω = quadVqS d L W v A z i (auxT d L W v ω) :=
  ⟨auxQuadChaos_chaos hv hA hz i ω, auxQuadChaos_Vq hA hz i ω⟩

/-- **The quadratic large deviation estimate (4.7) for any tag-free variance family and any
deterministic Hermitian shift `A`**, on the original coordinate space, through the auxiliary carrier:
for `Q_i = ∑_{k,l ≠ i} X_{ik} G^{(i)}_{kl} X_{li}` with `G^{(i)}` the minor resolvent of `A + X`,
and `V = ∑ σ_{ik} |G^{(i)}_{kl}|² σ_{il}`,
`P(λ V < |Q_i - ∑_k σ_{ik} G^{(i)}_{kk}|²) ≤ A_q / λ^{q+1}` under `gaussLaw v`.  The auxiliary
carrier is a proof device: the event is a function of `Xmat s` only.  RBM2D `gaussLaw_quad_tail`
(`AuxCarrier.lean:836`) is the case `A = 0`. -/
theorem gaussLaw_quad_tail {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v)
    {A : Matrix (Idx d L W) (Idx d L W) ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gaussLaw d L W v {s | lam * quadVqS d L W v A z i s < ‖quadQS d L W v A z i s‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have hA' : MeasurableSet
      {s : Ω d L W | lam * quadVqS d L W v A z i s < ‖quadQS d L W v A z i s‖ ^ 2} :=
    measurableSet_lt ((continuous_quadVqS v hA hz i).measurable.const_mul lam)
      ((continuous_quadQS v hA hz i).norm.pow 2).measurable
  have hmap : gaussLaw d L W v = (Sizes.seqP (auxSizes d)).map (auxT d L W v) :=
    (auxT_law d L W v).symm
  rw [hmap, Measure.map_apply (continuous_auxT d L W v).measurable hA']
  have := chaos_tail (auxQuadChaos d L W v hA hz i) hlam q
  refine le_trans (le_of_eq ?_) this
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, (auxQuadChaos_eq hv hA hz i ω).1,
    (auxQuadChaos_eq hv hA hz i ω).2]

/-- The entry variance of the GUE off the diagonal: `E|H_{ik}|² = N⁻¹`, `N = (W L)^d`. -/
theorem sigRow_gueVar {i k : Idx d L W} (hik : k ≠ i) :
    sigRow d L W (gueVar d L W) i k = ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := by
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  unfold sigRow rowCoordF
  split_ifs with h
  · have : i ≠ k := Ne.symm hik
    simp only [gueVar, this, ↓reduceIte]
    push_cast
    field_simp
  · simp only [gueVar, hik, ↓reduceIte]
    push_cast
    field_simp

/-- **The Gaussian quadratic-form LDE for the GUE rows (the probabilistic core of the Schur tail)**:
with `G^{(i)}` the resolvent of the minor, `Q_i = ∑_{k,l ≠ i} H_{ik} G^{(i)}_{kl} H_{li}` and
`N = (W L)^d`,
`P_{GUE}(λ N⁻² ∑_{kl} |G^{(i)}_{kl}|² < |Q_i - N⁻¹ tr G^{(i)}|²) ≤ A_q / λ^{q+1}` for every `λ > 0`,
`q`, `i` and `Im z ≠ 0`.  This is `gaussLaw_quad_tail` at `v = gueVar`, `A = 0`, i.e. the auxiliary
carrier supplies the GUE row chaos although no band profile is flat. -/
theorem gue_quad_tail {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gueP d L W {s | lam * ((((((W * L) ^ d : ℕ) : ℝ))⁻¹) ^ 2 *
        ∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
          ‖green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k l‖ ^ 2) <
      ‖(∑ k : {a : Idx d L W // a ≠ i}, ∑ l : {a : Idx d L W // a ≠ i},
          Xmat d L W s i k.1 * green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k l *
            Xmat d L W s l.1 i) -
        ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * ∑ k : {a : Idx d L W // a ≠ i},
          green ((Xmat d L W s).submatrix Subtype.val Subtype.val) z k k‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have h := gaussLaw_quad_tail (gueVar_tagFree d L W) (Matrix.isHermitian_zero) hz i hlam q
  rw [← gueP_eq_gaussLaw] at h
  convert h using 3
  ext s
  simp only [quadVqS, quadQS, zero_add]
  have e1 : ∀ k : {a : Idx d L W // a ≠ i}, sigRow d L W (gueVar d L W) i k.1
      = ((((W * L) ^ d : ℕ) : ℝ))⁻¹ := fun k => sigRow_gueVar k.2
  simp only [e1, ← Finset.mul_sum, ← Finset.sum_mul]
  constructor <;> intro hh <;> convert hh using 2 <;> ring

/-- **The model-class form of the quadratic LDE** (DECISIONS §57 (2)): for a model class `K`, the
mixture law `a S(K.lamV) + b N⁻¹` (`mixVar`) with the shift `(K.M sz).mean n`, i.e. the matrix `μ + X`
of the GUE-phase path and of the centred OU marginal `ouMatC`.  Band: `lamV = sz.lam`, mean `0`. -/
theorem kind_quad_tail (K : UNKind d) (sz : Sizes d) (n : ℕ) (a b : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d (sz.L n) (sz.W n)) {lam : ℝ} (hlam : 0 < lam) (q : ℕ) :
    gaussLaw d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (K.lamV sz n) a b)
      {s | lam * quadVqS d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (K.lamV sz n) a b)
          ((K.M sz).mean n) z i s <
        ‖quadQS d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (K.lamV sz n) a b)
          ((K.M sz).mean n) z i s‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) :=
  gaussLaw_quad_tail (mixVar_tagFree d (sz.L n) (sz.W n) (K.lamV sz n) a b)
    ((K.M sz).mean_herm n) hz i hlam q

end AuxRowChaos

/-! ## The rank-one row chaos on the auxiliary carrier (port of RBM1D `gueEntryLinChaos`)

Port of RBM1D `c06b103:RBM1D/Flow/GUEPhaseEntry.lean:1503–1550, 1647–1739`
(`gueEntryLinChaos`, `gueEntryLin_chaos`, `gueEntryLin_Vq`, `gueEntry_lin_tail_aux`) onto the
auxiliary carrier of §2, as §6c does for the quadratic chaos.  The row `(H_{ik})_{k ≠ i}` with a
coefficient vector `c` that does not read the row gives `Q = |∑_k H_{ik} c_k|² - ∑_k σ_{ik} |c_k|²`
and `V_q = (∑_k σ_{ik} |c_k|²)²`, where `σ_{ik} = sigRow v i k = E|H_{ik}|²` for a tag-free family
(`TagFree` replaces RBM1D's `GueEntryTagFree`, and `sigRow` replaces `S i k` together with the
hypothesis `GueEntryProfOK`; no resolvent enters `B`, so the hypothesis `z.im ≠ 0` is not needed).
No shift is needed: the cross terms `X_{i·} G^{(i)} A_{·i}` of the Schur complement of `A + X` are of
this form with `c = G^{(i)} A_{·i}` (off-row). -/

section AuxLin

open RBM.Green

/-- **The rank-one row chaos** at row `i` with coefficient vector `c`:
`B_{kl} = (λ_k c_k) conj(λ_l c_l)`; its chaos is `|∑_k H_{ik} c_k|² - ∑_k σ_{ik} |c_k|²`
(RBM1D `gueEntryLinChaos`, `GUEPhaseEntry.lean:1505`). -/
noncomputable def auxLinChaos (d L W : ℕ) [NeZero L] [NeZero W] (v : CoordF d L W → ℝ≥0)
    (i : Idx d L W)
    (c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ i} → ℂ)
    (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W i, ω x = ω' x) → c ω = c ω') :
    RowChaos (auxSizes d) {a : Idx d L W // a ≠ i} where
  co k b := auxRho d L W (rowCoordF d L W i k.1 b)
  co_inj := by
    rintro ⟨⟨k, hk⟩, b⟩ ⟨⟨l, hl⟩, c⟩ h
    obtain ⟨h1, h2⟩ := rowCoordF_injOn d L W hk hl (auxRho_injective d L W h)
    subst h1; subst h2; rfl
  gvar_tag k := by
    unfold rowCoordF
    split_ifs <;> exact_mod_cast (seqGvar_auxRho_tag d L W _ _).symm
  eps k := rowSignF d L W i k.1
  eps_sq k := by unfold rowSignF; split_ifs <;> norm_num
  r := 1
  B ω k l := ((lamRow d L W v i k.1 : ℝ) : ℂ) * c ω k *
    (starRingEnd ℂ) (((lamRow d L W v i l.1 : ℝ) : ℂ) * c ω l)
  B_cont k l := (continuous_const.mul (hc k)).mul
    (Complex.continuous_conj.comp (continuous_const.mul (hc l)))
  Bbd := ((∑ k : {a : Idx d L W // a ≠ i}, lamRow d L W v i k.1) * Cb) ^ 2
  B_bdd ω k l := by
    have hsum : ∀ k : {a : Idx d L W // a ≠ i},
        lamRow d L W v i k.1 ≤ ∑ k : {a : Idx d L W // a ≠ i}, lamRow d L W v i k.1 :=
      fun k => Finset.single_le_sum
        (f := fun k : {a : Idx d L W // a ≠ i} => lamRow d L W v i k.1)
        (fun k _ => lamRow_nonneg d L W v i k.1) (Finset.mem_univ k)
    have hb : ∀ k : {a : Idx d L W // a ≠ i}, ‖((lamRow d L W v i k.1 : ℝ) : ℂ) * c ω k‖
        ≤ (∑ k : {a : Idx d L W // a ≠ i}, lamRow d L W v i k.1) * Cb := by
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (lamRow_nonneg d L W v i k.1)]
      exact mul_le_mul (hsum k) (hCb ω k) (norm_nonneg _)
        ((lamRow_nonneg d L W v i k.1).trans (hsum k))
    rw [norm_mul, Complex.norm_conj, sq]
    exact mul_le_mul (hb k) (hb l) (norm_nonneg _) ((norm_nonneg _).trans (hb k))
  Ifree := auxOffRow d L W i
  Ifree_free k b := by
    classical
    unfold auxOffRow
    intro hmem
    obtain ⟨c, hc, hc'⟩ := Finset.mem_image.1 hmem
    have hc2 : c = rowCoordF d L W i k.1 b := auxRho_injective d L W hc'
    have hc3 := (Finset.mem_filter.1 hc).2
    rw [hc2] at hc3
    unfold rowCoordF at hc3
    split_ifs at hc3 with h
    · exact hc3.1 rfl
    · exact hc3.2 rfl
  B_free ω ω' h := by
    funext k l
    rw [hcf ω ω' h]

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem auxLin_sg_lam {v : CoordF d L W → ℝ≥0} (i : Idx d L W)
    (c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ i} → ℂ)
    (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W i, ω x = ω' x) → c ω = c ω')
    (k : {a : Idx d L W // a ≠ i}) :
    (auxLinChaos d L W v i c hc Cb hCb hcf).sg k * lamRow d L W v i k.1 ^ 2
      = sigRow d L W v i k.1 := by
  have h := auxScale_sq d L W v (rowCoordF d L W i k.1 true)
  change 2 * (1 : ℝ) ^ 2 *
      (Sizes.seqGvar (auxSizes d) (auxRho d L W (rowCoordF d L W i k.1 true)) : ℝ) *
      auxScale d L W v (rowCoordF d L W i k.1 true) ^ 2 = 2 * (v (rowCoordF d L W i k.1 true) : ℝ)
  rw [← h]
  ring

private theorem auxLin_h_lam {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v) (i : Idx d L W)
    (c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ i} → ℂ)
    (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W i, ω x = ω' x) → c ω = c ω')
    (ω : Sizes.SeqΩ (auxSizes d)) (k : {a : Idx d L W // a ≠ i}) :
    (lamRow d L W v i k.1 : ℂ) * (auxLinChaos d L W v i c hc Cb hCb hcf).h ω k
      = auxHG d L W v ω i k.1 := by
  rw [auxHG_apply d L W hv (Ne.symm k.2)]
  change _ * (((1 : ℝ) : ℂ) *
    ((ω (auxRho d L W (rowCoordF d L W i k.1 true)) : ℂ) +
      ((rowSignF d L W i k.1 : ℝ) : ℂ) * Complex.I *
      (ω (auxRho d L W (rowCoordF d L W i k.1 false)) : ℂ))) = _
  unfold lamRow
  push_cast
  ring

/-- **The rank-one chaos is `|∑ H_{ik} c_k|² - ∑ σ_{ik} |c_k|²`** (RBM1D `gueEntryLin_chaos`,
`GUEPhaseEntry.lean:1648`; `sigRow` for `S i k`, no `GueEntryProfOK`, no `z`). -/
theorem auxLin_chaos {v : CoordF d L W → ℝ≥0} (hv : TagFree d L W v) (i : Idx d L W)
    (c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ i} → ℂ)
    (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W i, ω x = ω' x) → c ω = c ω')
    (ω : Sizes.SeqΩ (auxSizes d)) :
    (auxLinChaos d L W v i c hc Cb hCb hcf).chaos ω
      = ((‖∑ k : {a : Idx d L W // a ≠ i}, auxHG d L W v ω i k.1 * c ω k‖ ^ 2
          - ∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2 : ℝ) : ℂ) := by
  have hY : ∀ k : {a : Idx d L W // a ≠ i},
      (auxLinChaos d L W v i c hc Cb hCb hcf).h ω k * ((lamRow d L W v i k.1 : ℂ) * c ω k)
        = auxHG d L W v ω i k.1 * c ω k := by
    intro k
    rw [← auxLin_h_lam hv i c hc Cb hCb hcf ω k]; ring
  unfold RowChaos.chaos RowChaos.cen
  have e1 : ∑ k, ∑ l, (auxLinChaos d L W v i c hc Cb hCb hcf).h ω k *
        (auxLinChaos d L W v i c hc Cb hCb hcf).B ω k l *
        (starRingEnd ℂ) ((auxLinChaos d L W v i c hc Cb hCb hcf).h ω l)
      = (∑ k, auxHG d L W v ω i k.1 * c ω k) *
        (starRingEnd ℂ) (∑ k, auxHG d L W v ω i k.1 * c ω k) := by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← hY k, ← hY l]
    change (auxLinChaos d L W v i c hc Cb hCb hcf).h ω k *
      (((lamRow d L W v i k.1 : ℝ) : ℂ) * c ω k *
      (starRingEnd ℂ) (((lamRow d L W v i l.1 : ℝ) : ℂ) * c ω l)) *
        (starRingEnd ℂ) ((auxLinChaos d L W v i c hc Cb hCb hcf).h ω l) = _
    rw [map_mul (starRingEnd ℂ) ((auxLinChaos d L W v i c hc Cb hCb hcf).h ω l)]
    ring
  have e2 : ∑ k, (((auxLinChaos d L W v i c hc Cb hCb hcf).sg k : ℝ) : ℂ) *
        (auxLinChaos d L W v i c hc Cb hCb hcf).B ω k k
      = ((∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← auxLin_sg_lam i c hc Cb hCb hcf k]
    change (((auxLinChaos d L W v i c hc Cb hCb hcf).sg k : ℝ) : ℂ) *
      (((lamRow d L W v i k.1 : ℝ) : ℂ) * c ω k *
        (starRingEnd ℂ) (((lamRow d L W v i k.1 : ℝ) : ℂ) * c ω k)) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (lamRow_nonneg d L W v i k.1)]
    push_cast
    ring
  rw [e1, e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The control of the rank-one chaos is `(∑ σ_{ik} |c_k|²)²`** (RBM1D `gueEntryLin_Vq`,
`GUEPhaseEntry.lean:1691`). -/
theorem auxLin_Vq {v : CoordF d L W → ℝ≥0} (i : Idx d L W)
    (c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ i} → ℂ)
    (hc : ∀ k, Continuous fun ω => c ω k)
    (Cb : ℝ) (hCb : ∀ ω k, ‖c ω k‖ ≤ Cb)
    (hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W i, ω x = ω' x) → c ω = c ω')
    (ω : Sizes.SeqΩ (auxSizes d)) :
    (auxLinChaos d L W v i c hc Cb hCb hcf).Vq ω
      = (∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2) ^ 2 := by
  have hpt : ∀ k l : {a : Idx d L W // a ≠ i},
      (auxLinChaos d L W v i c hc Cb hCb hcf).sg k *
        ‖(auxLinChaos d L W v i c hc Cb hCb hcf).B ω k l‖ ^ 2 *
        (auxLinChaos d L W v i c hc Cb hCb hcf).sg l
      = (sigRow d L W v i k.1 * ‖c ω k‖ ^ 2) * (sigRow d L W v i l.1 * ‖c ω l‖ ^ 2) := by
    intro k l
    rw [← auxLin_sg_lam (v := v) i c hc Cb hCb hcf k, ← auxLin_sg_lam (v := v) i c hc Cb hCb hcf l]
    change (auxLinChaos d L W v i c hc Cb hCb hcf).sg k *
      ‖((lamRow d L W v i k.1 : ℝ) : ℂ) * c ω k *
        (starRingEnd ℂ) (((lamRow d L W v i l.1 : ℝ) : ℂ) * c ω l)‖ ^ 2 *
      (auxLinChaos d L W v i c hc Cb hCb hcf).sg l = _
    rw [norm_mul, Complex.norm_conj, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (lamRow_nonneg d L W v i k.1),
      abs_of_nonneg (lamRow_nonneg d L W v i l.1)]
    ring
  change ∑ k, ∑ l, (auxLinChaos d L W v i c hc Cb hCb hcf).sg k *
      ‖(auxLinChaos d L W v i c hc Cb hCb hcf).B ω k l‖ ^ 2 *
      (auxLinChaos d L W v i c hc Cb hCb hcf).sg l = _
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hpt k l

/-- **A rank-one chaos `Q = Y - R`, `V_q = R²`**: `P(Λ R < Y) ≤ A_q / ((Λ - 1)²)^{q+1}` for
`Λ > 1` (RBM1D `gueEntry_lin_tail_aux`, `GUEPhaseEntry.lean:1723`, with `P D ↦ seqP sz`). -/
theorem aux_lin_tail {d : ℕ} {sz : Sizes d} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : RowChaos sz κ) (Y R : Sizes.SeqΩ sz → ℝ) (hR0 : ∀ ω, 0 ≤ R ω)
    (hchaos : ∀ ω, C.chaos ω = ((Y ω - R ω : ℝ) : ℂ)) (hV : ∀ ω, C.Vq ω = R ω ^ 2)
    {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    (Sizes.seqP sz) {ω | Λ * R ω < Y ω}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  have hlam : 0 < (Λ - 1) ^ 2 := by
    have : 0 < Λ - 1 := by linarith
    positivity
  refine (measure_mono ?_).trans (chaos_tail C hlam q)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hV, hchaos, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h0 := hR0 ω
  have h1 : (Λ - 1) * R ω < Y ω - R ω := by linarith
  have h2 : 0 ≤ (Λ - 1) * R ω := mul_nonneg (by linarith) h0
  have h3 := pow_lt_pow_left₀ h1 h2 (by norm_num : (2 : ℕ) ≠ 0)
  nlinarith [h3]

end AuxLin

/-! ## Compiled nonempty instances (T2196; CLAUDE.md §4 step 2)

`d = 3`, `L = 3`, `W = 2` (`N = (W L)^d = 216`, a row of 215 indices), `z = Complex.I`, row `0`.
Every deterministic hypothesis is discharged: `3 ≤ L` is `3 ≤ 3`, tag-freeness is `rfl`, `A` is
`0` or `1` (Hermitian), `z.im ≠ 0`, `0 < lam`, `1 < Λ`.  No `decide` over `Idx`.  The bounds are
`A_0 / 4 = 1/2` and `A_0 / (3 - 1)² = 1/2` (`inst_bounds`), so no conclusion is trivially true. -/

namespace AuxCarrierCheck

open RBM.Green

/-- Two points of one block of `Idx 3 3 2` (`W = 2`: the coordinates `0` and `1` of `Z_6` are in
block `0`) have a positive variance, at any coupling (here `1/2`). -/
theorem inst_svarF_pos_of_block_eq :
    0 < svarF 3 3 2 (1 / 2) (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  svarF_pos_of_block_eq 3 3 2 (1 / 2) _ _ (by
    funext k
    fin_cases k <;> decide)

/-- **The auxiliary carrier at `d = 3`**: the auxiliary variance is positive on the image of the
embedding (two points of `Idx 3 3 2`). -/
theorem inst_aux_pos :
    0 < svarF 3 ((auxSizes 3).L (auxSlot 3 2)) ((auxSizes 3).W (auxSlot 3 2)) 0
      (auxEmb 3 3 2 (0 : Idx 3 3 2)) (auxEmb 3 3 2 (![1, 2, 3] : Idx 3 3 2)) :=
  svarF_aux_pos 3 3 2 _ _

/-- **Realisation of the GUE variances** by the auxiliary carrier at `d = 3`, `L = 3`, `W = 2`. -/
theorem inst_auxT_law :
    (Sizes.seqP (auxSizes 3)).map (auxT 3 3 2 (gueVar 3 3 2))
      = Measure.infinitePi (fun c : CoordF 3 3 2 => gaussianReal 0 (gueVar 3 3 2 c)) :=
  auxT_law 3 3 2 (gueVar 3 3 2)

/-- The auxiliary matrix has the law of the GUE matrix at `d = 3`, `L = 3`, `W = 2`. -/
theorem inst_auxHG_law :
    (Sizes.seqP (auxSizes 3)).map (auxHG 3 3 2 (gueVar 3 3 2))
      = (gueP 3 3 2).map (Xmat 3 3 2) :=
  auxHG_law 3 3 2 (gueVar 3 3 2)

/-- The realisation theorem at a mixture family (`mixVar` at the profile coupling `1/2`). -/
theorem inst_exists_seqP_map_eq_gaussLaw :
    ∃ (sz : Sizes 3) (T : Sizes.SeqΩ sz → Ω 3 3 2), Continuous T ∧
      (Sizes.seqP sz).map T = gaussLaw 3 3 2 (mixVar 3 3 2 (1 / 2) (1 / 2) (1 / 2)) :=
  exists_seqP_map_eq_gaussLaw 3 3 2 (mixVar 3 3 2 (1 / 2) (1 / 2) (1 / 2))

/-- **The generic tail `chaos_tail`** for the quadratic row chaos of the auxiliary matrix at
`d = 3`, `L = 3`, `W = 2`, `v = gueVar 3 3 2`, `A = 0`, `z = i`, row `0`, `λ = 4`, `q = 0`
(bound `1/2`). -/
theorem inst_chaos_tail :
    (Sizes.seqP (auxSizes 3)) {ω | 4 * (auxQuadChaos 3 3 2 (gueVar 3 3 2) (A := 0)
        Matrix.isHermitian_zero (z := Complex.I) (by simp) (0 : Idx 3 3 2)).Vq ω <
      ‖(auxQuadChaos 3 3 2 (gueVar 3 3 2) (A := 0) Matrix.isHermitian_zero
        (z := Complex.I) (by simp) (0 : Idx 3 3 2)).chaos ω‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst 0 / 4 ^ (0 + 1)) :=
  chaos_tail (auxQuadChaos 3 3 2 (gueVar 3 3 2) (A := 0) Matrix.isHermitian_zero
    (z := Complex.I) (by simp) (0 : Idx 3 3 2)) (by norm_num) 0

/-- **The GUE quadratic LDE** (`gue_quad_tail`) at `d = 3`, `L = 3`, `W = 2` (`N = 216`),
`z = i`, row `0`, `λ = 4`, `q = 0`. -/
theorem inst_gue_quad_tail :
    gueP 3 3 2 {s | 4 * ((((((2 * 3) ^ 3 : ℕ) : ℝ))⁻¹) ^ 2 *
        ∑ k : {a : Idx 3 3 2 // a ≠ 0}, ∑ l : {a : Idx 3 3 2 // a ≠ 0},
          ‖green ((Xmat 3 3 2 s).submatrix Subtype.val Subtype.val) Complex.I k l‖ ^ 2) <
      ‖(∑ k : {a : Idx 3 3 2 // a ≠ 0}, ∑ l : {a : Idx 3 3 2 // a ≠ 0},
          Xmat 3 3 2 s 0 k.1 *
            green ((Xmat 3 3 2 s).submatrix Subtype.val Subtype.val) Complex.I k l *
            Xmat 3 3 2 s l.1 0) -
        ((((2 * 3) ^ 3 : ℕ) : ℝ))⁻¹ * ∑ k : {a : Idx 3 3 2 // a ≠ 0},
          green ((Xmat 3 3 2 s).submatrix Subtype.val Subtype.val) Complex.I k k‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst 0 / 4 ^ (0 + 1)) :=
  gue_quad_tail (d := 3) (L := 3) (W := 2) (z := Complex.I) (by simp) 0 (lam := 4)
    (by norm_num) 0

/-- The same estimate for the band variances `v = gvarF 3 3 2 (1/2)` (`A = 0`) through the
auxiliary carrier. -/
theorem inst_band_quad_tail :
    gaussLaw 3 3 2 (gvarF 3 3 2 (1 / 2)) {s | 4 * quadVqS 3 3 2 (gvarF 3 3 2 (1 / 2)) 0
        Complex.I 0 s <
      ‖quadQS 3 3 2 (gvarF 3 3 2 (1 / 2)) 0 Complex.I 0 s‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst 0 / 4 ^ (0 + 1)) :=
  gaussLaw_quad_tail (d := 3) (L := 3) (W := 2) (v := gvarF 3 3 2 (1 / 2))
    (gvarF_tagFree 3 3 2 (1 / 2)) Matrix.isHermitian_zero (z := Complex.I) (by simp) 0
    (lam := 4) (by norm_num) 0

/-- **The shifted LDE** at the mixture family `mixVar 3 3 2 0 (1/2) (1/2)` (profile coupling `0`,
the BA profile) and the deterministic Hermitian shift `A = 1`, `λ = 4`, `q = 0`. -/
theorem inst_shift_quad_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 0 (1 / 2) (1 / 2)) {s |
        4 * quadVqS 3 3 2 (mixVar 3 3 2 0 (1 / 2) (1 / 2)) 1 Complex.I 0 s <
      ‖quadQS 3 3 2 (mixVar 3 3 2 0 (1 / 2) (1 / 2)) 1 Complex.I 0 s‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst 0 / 4 ^ (0 + 1)) :=
  gaussLaw_quad_tail (d := 3) (L := 3) (W := 2) (v := mixVar 3 3 2 0 (1 / 2) (1 / 2))
    (mixVar_tagFree 3 3 2 0 (1 / 2) (1 / 2)) (Matrix.isHermitian_one) (z := Complex.I)
    (by simp) 0 (lam := 4) (by norm_num) 0

/-- **The model-class form** at the band kind `UNKind.band 3` over the preflight sequence
`SizesInst.sz0` (`n = 0`: `(L, W) = (4, 32)`, `N = 2^21`), `a = b = 1/2`, `z = i`, `λ = 4`,
`q = 0`; the size index `n` and the row `i : Idx 3 (sz0.L n) (sz0.W n)` are variables. -/
theorem inst_kind_quad_tail_band (n : ℕ) (i : Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) :
    gaussLaw 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
        (mixVar 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
          ((UNKind.band 3).lamV SizesInst.sz0 n) (1 / 2) (1 / 2))
      {s | 4 * quadVqS 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
          (mixVar 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
            ((UNKind.band 3).lamV SizesInst.sz0 n) (1 / 2) (1 / 2))
          (((UNKind.band 3).M SizesInst.sz0).mean n) Complex.I i s <
        ‖quadQS 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
          (mixVar 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
            ((UNKind.band 3).lamV SizesInst.sz0 n) (1 / 2) (1 / 2))
          (((UNKind.band 3).M SizesInst.sz0).mean n) Complex.I i s‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst 0 / 4 ^ (0 + 1)) :=
  kind_quad_tail (UNKind.band 3) SizesInst.sz0 n (1 / 2) (1 / 2) (z := Complex.I) (by simp) i
    (lam := 4) (by norm_num) 0

/-- At `n = 0` the size of `inst_kind_quad_tail_band` is `N = 2^21`, `(L, W) = (4, 32)`. -/
theorem inst_kind_quad_tail_band_size :
    SizesInst.sz0.L 0 = 4 ∧ SizesInst.sz0.W 0 = 32 ∧ SizesInst.sz0.size 0 = 2 ^ 21 := by
  obtain ⟨h1, h2, h3, -⟩ := SizesInst.sz0_values
  exact ⟨h1, h2, by rw [h3]; norm_num⟩

/-- **The rank-one tail** `aux_lin_tail` at `d = 3`, `L = 3`, `W = 2` (`N = 216`),
`v = gueVar 3 3 2`, row `0`, `c ≡ 1`, `C_b = 1`, `Λ = 3`, `q = 0`: with `Y = |∑_k H_{0k}|²` and
`R = ∑_k σ_{0k}`, `P(3 R < Y) ≤ A_0 / ((3 - 1)²)^1 = 1/2`. -/
theorem inst_aux_lin_tail :
    (Sizes.seqP (auxSizes 3)) {ω | 3 * (∑ k : {a : Idx 3 3 2 // a ≠ 0},
          sigRow 3 3 2 (gueVar 3 3 2) 0 k.1 * ‖(1 : ℂ)‖ ^ 2) <
        ‖∑ k : {a : Idx 3 3 2 // a ≠ 0}, auxHG 3 3 2 (gueVar 3 3 2) ω 0 k.1 * (1 : ℂ)‖ ^ 2}
      ≤ ENNReal.ofReal (hwConst 0 / ((3 - 1) ^ 2) ^ (0 + 1)) :=
  aux_lin_tail
    (auxLinChaos 3 3 2 (gueVar 3 3 2) (0 : Idx 3 3 2) (fun _ _ => 1) (fun _ => continuous_const) 1
      (fun _ _ => by simp) (fun _ _ _ => rfl))
    (fun ω => ‖∑ k : {a : Idx 3 3 2 // a ≠ 0}, auxHG 3 3 2 (gueVar 3 3 2) ω 0 k.1 * (1 : ℂ)‖ ^ 2)
    (fun _ => ∑ k : {a : Idx 3 3 2 // a ≠ 0}, sigRow 3 3 2 (gueVar 3 3 2) 0 k.1 * ‖(1 : ℂ)‖ ^ 2)
    (fun _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (by unfold sigRow; positivity) (by positivity))
    (fun ω => auxLin_chaos (gueVar_tagFree 3 3 2) 0 _ _ 1 _ _ ω)
    (fun ω => auxLin_Vq 0 _ _ 1 _ _ ω) (by norm_num) 0

/-- **The row sums of the mixture profile** at `d = 3`, `L = 3`, `W = 2` (`3 ≤ 3`), `g = 1/2`,
`a = b = 1/2`, row `0`: `∑_j S_{0j} = a + b`. -/
theorem inst_sum_Smix_row :
    ∑ j : Idx 3 3 2, (1 / 2 * svarF 3 3 2 (1 / 2) (0 : Idx 3 3 2) j +
      (1 / 2) / ((((2 * 3) ^ 3 : ℕ)) : ℝ)) = 1 / 2 + 1 / 2 :=
  sum_Smix_row 3 3 2 (by norm_num) (1 / 2) (1 / 2) (1 / 2) 0

/-- The merged `ouVar` is `mixVar g (e^{-t}) (1 - e^{-t})` (`rfl`), at `d = 3`, `L = 3`, `W = 2`. -/
theorem inst_mixVar_exp_eq_ouVar (t : ℝ) (c : CoordF 3 3 2) :
    mixVar 3 3 2 (1 / 2) (Real.exp (-t)) (1 - Real.exp (-t)) c = ouVar 3 3 2 (1 / 2) t c :=
  mixVar_exp_eq_ouVar 3 3 2 (1 / 2) t c

/-- The instance bounds are nontrivial (`1/2 < 1`): `A_0 / 4 = 1/2` (`inst_chaos_tail`,
`inst_gue_quad_tail`, `inst_shift_quad_tail`, `inst_kind_quad_tail_band`) and
`A_0 / (3 - 1)² = 1/2` (`inst_aux_lin_tail`). -/
theorem inst_bounds :
    hwConst 0 / (4 : ℝ) ^ (0 + 1) = 1 / 2 ∧
      hwConst 0 / (((3 : ℝ) - 1) ^ 2) ^ (0 + 1) = 1 / 2 := by
  norm_num [hwConst]

end AuxCarrierCheck

end RBM.Univ
