/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.EntryDet

/-!
# The probabilistic half of Lemma 4.1 at the mixture profile, first half, `d ≥ 3` (T2293, UN-41)

Port of `RBM2D/Universality/GUEPhase/EntryTail.lean` at `c9a24cf`, lines `1-874` (the carrier, law,
profile and large-deviation-tail layer, and the deterministic bridge), to `d ≥ 3`.  The second half
(`:876-1525`: the union of the failure events, the size scale and `gueEntryMix`) is T2293b
(`EntryTailMain.lean`).

* the mixture matrix `mixMat sz n a b ω = √a X_band(ω₁) + √b X_GUE(ω₂)` on the band OU carrier
  `ouP (UNModel.band sz) n` (`SeqΩ sz × Ω d (L n) (W n)`, the band coordinates are read through
  `slice sz n`, the coupling is `sz.lam n`), `ouMat_eq_mixMat`, and the pin `GUEEntryMix d`;
* `mixSample`, its Gaussian law `mixSample_law` (every `a, b ≥ 0`), the profile identities
  (`sigRow (mixVar g a b) i k = Smix g a b i k`, diagonal variance, positivity), `MixProfOK`;
* the four large-deviation tails under `gaussLaw v` (quadratic form through `gaussLaw_quad_tail` at
  the shift `A = 0`; row and column through the rank-one chaos `auxLinChaos`; diagonal by Chernoff),
  generic in a tag-free `v` and a profile `S` with `MixProfOK`;
* `mixEntry_greenBlk_eq` and the deterministic step `mixEntry_det` (`mix_det` on `Idx`, relabelled
  by `splitEquiv`).

The `d ≥ 3` changes against RBM2D: the carrier (`ouP L W` on `Ω L W × Ω L W`, no coupling, becomes
`ouP (UNModel.band sz) n` with coupling `sz.lam n`), `W^{-2} ↦ W^{-d}`, `(W L)^2 ↦ (W L)^d`,
`Admissible 𝔠 d ↦ sz.Admissible 𝔠 𝔡` (with `WO 𝔡`), and the interface of `mix_det`
(`hd : 3 ≤ d`, `0 < g ≤ Λ`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss RBM.Green
open scoped NNReal ENNReal

/-! ## §7 The pin: Lemma 4.1 for the mixture profile -/

section PinEntry

variable {d : ℕ}

/-- The mixture matrix `√a X_band + √b X_GUE` on the OU carrier `ouP = seqP ⊗ gueP` of the band model:
its entry variance profile is `a S(g) + b N⁻¹` (`Smix`), `g = sz.lam n`.  With `(a, b) = (t₁, u - t₁)`
it is the one-time law of the GUE-phase grid path; with `(a, b) = (e^{-t}, 1 - e^{-t})` it is the OU
marginal `ouMat t` (`ouMat_eq_mixMat`).  RBM2D `:75`; the band matrix is `seqXmat sz n ω.1`. -/
def mixMat (sz : Sizes d) (n : ℕ) (a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Real.sqrt a • Sizes.seqXmat sz n ω.1 + Real.sqrt b • Xmat d (sz.L n) (sz.W n) ω.2

theorem mixMat_isHermitian (sz : Sizes d) (n : ℕ) (a b : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : (mixMat sz n a b ω).IsHermitian :=
  ((Sizes.seqXmat_isHermitian sz n ω.1).smul (IsSelfAdjoint.all _)).add
    ((Xmat_isHermitian d _ _ ω.2).smul (IsSelfAdjoint.all _))

theorem ouMat_eq_mixMat (sz : Sizes d) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat (UNModel.band sz) n t ω = mixMat sz n (Real.exp (-t)) (1 - Real.exp (-t)) ω := by
  have h : Real.sqrt (Real.exp (-t)) = Real.exp (-t / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _), ← Real.exp_add]
    congr 1; ring
  simp only [ouMat, mixMat, UNModel.band, h]

/-- **Extreme input `ζ = 0`**: `b = 0` is the (scaled) band matrix. -/
theorem mixMat_zero_right (sz : Sizes d) (n : ℕ) (a : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    mixMat sz n a 0 ω = Real.sqrt a • Sizes.seqXmat sz n ω.1 := by
  simp [mixMat]

/-- **Extreme input `ζ = 1`**: `a = 0` is the (scaled) flat GUE matrix (no band structure). -/
theorem mixMat_zero_left (sz : Sizes d) (n : ℕ) (b : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    mixMat sz n 0 b ω = Real.sqrt b • Xmat d (sz.L n) (sz.W n) ω.2 := by
  simp [mixMat]

end PinEntry

/-- **Pin `GUEEntryMix d`** (the output of the probabilistic half of Lemma 4.1 at the mixture profile,
as its consumers use it).  Lemma 4.1 (4.2)+(4.3) of [YY_25] for the profile `S_u = a S(g) + b N⁻¹`,
`u = a + b < 1`, `g = sz.lam n`, at a polynomially large family of mixture parameters
`(a_{n,k}, b_{n,k})`, `k ≤ K_n ≤ N^{n0}`, in the one-time-law form on `ouP (UNModel.band sz) n` (the union
over the grid is inside the probability): on the a priori event `‖G - m‖_max ≤ δ_n`, `δ_n ≤ N^{-c₀}`,
`|G_ij - m δ_ij|² ≺ max_{a,b} |𝓛_{(+,-),(a,b)}| + W^{-d}`, at the energy `E_n` and the spectral parameter
`z_u^{(E)}` with `u = a + b`.  `b = 0` is the band statement, `a = 0` the flat GUE.  Paper:
`lem_GbEXP` (`3_5:14`, "follows Lemma 4.1 of [YY_25]"), `1_2:566-570`.  RBM2D `:112`
(`W⁻² ↦ W^{-d}`; `Admissible 𝔠 d ↦ sz.Admissible 𝔠 𝔡`; `3 ≤ d` is not part of the pin). -/
def GUEEntryMix (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ n0 : ℕ, ∀ K : ℕ → ℕ,
  (∀ n, K n ≤ (sz.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ,
  (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) →
  ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) →
  (∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) →
  ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
    ouP (UNModel.band sz) n
      {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
        ((sz.size n : ℕ) : ℝ) ^ τ *
            (maxLoopPM d (sz.L n) (sz.W n) (E n) (a n k + b n k)
                (mixMat sz n (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
          (if ∀ x y, llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k)
                (mixMat sz n (a n k) (b n k) ω) x y ≤ δ n
            then llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k)
                  (mixMat sz n (a n k) (b n k) ω) i j ^ 2
            else 0)} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-! ## Part 2.1 The coordinates of the mixture matrix and their law -/

section MixSample

variable {d : ℕ}

/-- The real coordinates `√a (slice ω₁) + √b ω₂` of the mixture matrix `mixMat a b` on the OU carrier
(RBM2D `:142`; the band coordinates are read through `slice sz n`). -/
def mixSample (sz : Sizes d) (n : ℕ) (a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Ω d (sz.L n) (sz.W n) :=
  fun c => Real.sqrt a * Sizes.slice sz n ω.1 c + Real.sqrt b * ω.2 c

theorem measurable_mixSample (sz : Sizes d) (n : ℕ) (a b : ℝ) : Measurable (mixSample sz n a b) := by
  refine measurable_pi_iff.2 fun c => ?_
  have h1 : Measurable fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) => Sizes.slice sz n ω.1 c :=
    ((measurable_pi_apply c).comp (Sizes.measurable_slice sz n)).comp measurable_fst
  have h2 : Measurable fun ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) => ω.2 c :=
    (measurable_pi_apply c).comp measurable_snd
  exact (h1.const_mul _).add (h2.const_mul _)

/-- `mixMat a b = Xmat (√a slice ω₁ + √b ω₂)` (as `ouMat_eq_Xmat_ouSample`, by `Xmat_add`, `Xmat_smul`). -/
theorem mixMat_eq_Xmat_mixSample (sz : Sizes d) (n : ℕ) (a b : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    mixMat sz n a b ω = Xmat d (sz.L n) (sz.W n) (mixSample sz n a b ω) := by
  have h : mixSample sz n a b ω =
      Real.sqrt a • Sizes.slice sz n ω.1 + Real.sqrt b • ω.2 := by
    funext c
    simp [mixSample]
  rw [h, Xmat_add, Xmat_smul, Xmat_smul]
  rfl

theorem measurable_mixMat (sz : Sizes d) (n : ℕ) (a b : ℝ) : Measurable (mixMat sz n a b) := by
  have hX : Measurable (Xmat d (sz.L n) (sz.W n)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      measurable_Xentry d (sz.L n) (sz.W n) i j
  have h : mixMat sz n a b = Xmat d (sz.L n) (sz.W n) ∘ mixSample sz n a b := by
    funext ω
    exact mixMat_eq_Xmat_mixSample sz n a b ω
  rw [h]
  exact hX.comp (measurable_mixSample sz n a b)

end MixSample

/-- The law of `α X + β Y` for independent centred Gaussians `X`, `Y` (copy of the private
`ou_pair_map` of `Universality/OU.lean`). -/
private theorem mixEntry_pair_map (a b : ℝ) (v₁ v₂ : ℝ≥0) :
    ((gaussianReal 0 v₁).prod (gaussianReal 0 v₂)).map
        (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      gaussianReal 0
        (NNReal.mk (a ^ 2) (sq_nonneg a) * v₁ + NNReal.mk (b ^ 2) (sq_nonneg b) * v₂) := by
  have h : (fun p : ℝ × ℝ => a * p.1 + b * p.2) =
      (fun q : ℝ × ℝ => q.1 + q.2) ∘ Prod.map (fun x : ℝ => a * x) (fun y : ℝ => b * y) := by
    funext p
    rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  have := gaussianReal_conv_gaussianReal (m₁ := a * 0) (m₂ := b * 0)
    (v₁ := NNReal.mk (a ^ 2) (sq_nonneg a) * v₁) (v₂ := NNReal.mk (b ^ 2) (sq_nonneg b) * v₂)
  rw [mul_zero] at this
  simpa [Measure.conv] using this

section MixSampleLaw

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- The mixture on the pair space `Ω × Ω` (the source form of `mixSample`; helper). -/
private def mixSamplePair (a b : ℝ) (ω : Ω d L W × Ω d L W) : Ω d L W :=
  fun c => Real.sqrt a * ω.1 c + Real.sqrt b * ω.2 c

private theorem measurable_mixSamplePair (a b : ℝ) : Measurable (mixSamplePair d L W a b) := by
  refine measurable_pi_iff.2 fun c => ?_
  have h1 : Measurable fun ω : Ω d L W × Ω d L W => ω.1 c :=
    (measurable_pi_apply c).comp measurable_fst
  have h2 : Measurable fun ω : Ω d L W × Ω d L W => ω.2 c :=
    (measurable_pi_apply c).comp measurable_snd
  exact (h1.const_mul _).add (h2.const_mul _)

/-- The one-time Gaussian law on the pair space `PF g ⊗ gueP`, every `a, b ≥ 0` (the body of RBM2D
`mixSample_law`, `:202-262`, with `P` replaced by `PF d L W g`; copy of the private `ouSamplePair_law` of
`Universality/OU.lean` with `(√a, √b)` for `(e^{-t/2}, √(1 - e^{-t}))`). -/
private theorem mixSamplePair_law {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((PF d L W g).prod (gueP d L W)).map (mixSamplePair d L W a b) =
      gaussLaw d L W (mixVar d L W g a b) := by
  have hA : NNReal.mk (Real.sqrt a ^ 2) (sq_nonneg _) = a.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ ha]
    exact Real.sq_sqrt ha
  have hB : NNReal.mk (Real.sqrt b ^ 2) (sq_nonneg _) = b.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_mk, Real.coe_toNNReal _ hb]
    exact Real.sq_sqrt hb
  refine IsProjectiveLimit.unique ?_
    (Measure.isProjectiveLimit_infinitePi (fun c => gaussianReal 0 (mixVar d L W g a b c)))
  intro I
  set α : ℝ := Real.sqrt a with hα
  set β : ℝ := Real.sqrt b with hβ
  let f : ℝ × ℝ → ℝ := fun p => α * p.1 + β * p.2
  have hf : Measurable f := by fun_prop
  let R : (Ω d L W × Ω d L W) → (I → ℝ) × (I → ℝ) := Prod.map I.restrict I.restrict
  let g' : (I → ℝ) × (I → ℝ) → (I → ℝ) := fun q i => α * q.1 i + β * q.2 i
  have hR : Measurable R := (Finset.measurable_restrict I).prodMap (Finset.measurable_restrict I)
  have hg : Measurable g' := by
    refine measurable_pi_iff.2 fun i => ?_
    have h1 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.1 i :=
      (measurable_pi_apply i).comp measurable_fst
    have h2 : Measurable fun q : (I → ℝ) × (I → ℝ) => q.2 i :=
      (measurable_pi_apply i).comp measurable_snd
    exact (h1.const_mul _).add (h2.const_mul _)
  have hcomp : (fun ω : Ω d L W => I.restrict ω) ∘ mixSamplePair d L W a b = g' ∘ R := by
    funext ω
    rfl
  have hR_map : ((PF d L W g).prod (gueP d L W)).map R =
      (Measure.pi fun i : I => gaussianReal 0 (gvarF d L W g i)).prod
        (Measure.pi fun i : I => gaussianReal 0 (gueVar d L W i)) := by
    have h1 : (PF d L W g).map I.restrict =
        Measure.pi fun i : I => gaussianReal 0 (gvarF d L W g i) :=
      Measure.infinitePi_map_restrict _
    have h2 : (gueP d L W).map I.restrict =
        Measure.pi fun i : I => gaussianReal 0 (gueVar d L W i) :=
      Measure.infinitePi_map_restrict _
    rw [← h1, ← h2, Measure.map_prod_map _ _ (Finset.measurable_restrict I)
      (Finset.measurable_restrict I)]
  have he_map := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ I
    (fun i : I => gaussianReal 0 (gvarF d L W g i))
    (fun i : I => gaussianReal 0 (gueVar d L W i))).map_eq
  have hge : g' ∘ (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I) = fun x i => f (x i) := by
    funext x i
    rfl
  have : ∀ i : I, SigmaFinite
      (((gaussianReal 0 (gvarF d L W g i)).prod (gaussianReal 0 (gueVar d L W i))).map f) :=
    fun i => by
    rw [mixEntry_pair_map]
    infer_instance
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_mixSamplePair d L W a b), hcomp,
    ← Measure.map_map hg hR, hR_map, ← he_map, Measure.map_map hg
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ I).measurable, hge,
    Measure.pi_map_pi (fun i => hf.aemeasurable)]
  congr 1
  funext i
  rw [mixEntry_pair_map, hA, hB]
  rfl

end MixSampleLaw

section MixSampleLawBand

variable {d : ℕ}

/-- **The one-time Gaussian law of the mixture, for every `a, b ≥ 0`** (RBM2D `mixSample_law`, `:202`;
the merged `ouSample_law` is the case `(a, b) = (e^{-t}, 1 - e^{-t})`, `a > 0`, `a + b = 1`, and does
not contain `a = 0` or `a + b < 1`): under `ouP (UNModel.band sz) n` the coordinates `√a (slice ω₁) +
√b ω₂` are independent centred Gaussians of variance `a gvarF_c(sz.lam n) + b gueVar_c = mixVar … a b c`.
Proof: the pair-space law above, transported by `Prod.map (slice sz n) id` as in `ouSample_law`. -/
theorem mixSample_law (sz : Sizes d) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (ouP (UNModel.band sz) n).map (mixSample sz n a b) =
      gaussLaw d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (sz.lam n) a b) := by
  have h : mixSample sz n a b =
      mixSamplePair d (sz.L n) (sz.W n) a b ∘ Prod.map (Sizes.slice sz n) id := rfl
  have hm : Measurable (Prod.map (Sizes.slice sz n) (id : Ω d (sz.L n) (sz.W n) → _)) :=
    (Sizes.measurable_slice sz n).prodMap measurable_id
  rw [h, ← Measure.map_map (measurable_mixSamplePair _ _ _ a b) hm]
  have : (ouP (UNModel.band sz) n).map (Prod.map (Sizes.slice sz n) id) =
      (PF d (sz.L n) (sz.W n) (sz.lam n)).prod (gueP d (sz.L n) (sz.W n)) := by
    unfold ouP
    rw [← Measure.map_prod_map _ _ (Sizes.measurable_slice sz n) measurable_id, Measure.map_id]
    change ((Sizes.seqP sz).map (Sizes.slice sz n)).prod _ = _
    rw [Sizes.seqP_map_slice]
  rw [this]
  exact mixSamplePair_law d (sz.L n) (sz.W n) (sz.lam n) ha hb

/-- The transfer of a tail bound from `gaussLaw (mixVar a b)` to the carrier `ouP`: for a
measurable event `A` of the coordinates, `ouP (mixSample⁻¹ A) = gaussLaw (mixVar a b) A`. -/
theorem ouP_mixSample_preimage (sz : Sizes d) (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {A : Set (Ω d (sz.L n) (sz.W n))} (hA : MeasurableSet A) :
    ouP (UNModel.band sz) n (mixSample sz n a b ⁻¹' A) =
      gaussLaw d (sz.L n) (sz.W n) (mixVar d (sz.L n) (sz.W n) (sz.lam n) a b) A := by
  rw [← mixSample_law sz n ha hb, Measure.map_apply (measurable_mixSample sz n a b) hA]

end MixSampleLawBand

/-! ## Part 2.2 The entry variances of the mixture (the profile `Smix`) -/

section MixVarId

variable (d L W : ℕ) [NeZero L] [NeZero W]

theorem mixEntry_mixVar_coe (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (c : CoordF d L W) :
    (mixVar d L W g a b c : ℝ) = a * (gvarF d L W g c : ℝ) + b * (gueVar d L W c : ℝ) := by
  simp [mixVar, Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]

/-- `sigRow (gvarF g) i k = S_{ik}` for `k ≠ i` (two real coordinates of variance `S_{ik}/2`).
RBM2D `mixEntry_sigRow_gvar` (`:286`), renamed. -/
theorem mixEntry_sigRow_gvarF (g : ℝ) {i k : Idx d L W} (hik : k ≠ i) :
    sigRow d L W (gvarF d L W g) i k = svarF d L W g i k := by
  have hoff : ∀ x y : Idx d L W, x ≠ y →
      ((gvarF d L W g (x, y, true) : ℝ≥0) : ℝ) = svarF d L W g x y / 2 := fun x y hxy => by
    simp [gvarF, hxy]
    rfl
  unfold sigRow rowCoordF
  split_ifs with h
  · rw [hoff i k (Ne.symm hik)]
    ring
  · rw [hoff k i hik, svarF_comm d L W g k i]
    ring

/-- **The entry variance of the mixture**: `E|H_{ik}|² = 2 (a gvarF_c + b gueVar_c) = a S_{ik} + b N⁻¹ =
Smix g a b i k` for `k ≠ i`. -/
theorem mixEntry_sigRow_mixVar (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {i k : Idx d L W}
    (hik : k ≠ i) :
    sigRow d L W (mixVar d L W g a b) i k = Smix d L W g a b i k := by
  have h : sigRow d L W (mixVar d L W g a b) i k = a * sigRow d L W (gvarF d L W g) i k
      + b * sigRow d L W (gueVar d L W) i k := by
    unfold sigRow
    rw [mixEntry_mixVar_coe d L W g ha hb]
    ring
  rw [h, mixEntry_sigRow_gvarF d L W g hik, sigRow_gueVar hik]
  unfold Smix
  rw [div_eq_mul_inv]

/-- The diagonal variance of the mixture: `E (X_{ii})² = a S_{ii} + b N⁻¹ = Smix g a b i i`. -/
theorem mixEntry_mixVar_diag (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (i : Idx d L W) :
    (mixVar d L W g a b (i, i, true) : ℝ) = Smix d L W g a b i i := by
  rw [mixEntry_mixVar_coe d L W g ha hb]
  have hgd : ((gvarF d L W g (i, i, true) : ℝ≥0) : ℝ) = svarF d L W g i i := by
    simp [gvarF]
    rfl
  have hN : (((W * L) ^ d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  rw [hgd]
  unfold Smix
  simp only [gueVar, ite_true]
  push_cast
  rw [div_eq_mul_inv]

theorem mixEntry_Smix_diag_pos (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (i : Idx d L W) : 0 < Smix d L W g a b i i := by
  have hW : (0 : ℝ) < W := Nat.cast_pos.2 (NeZero.pos W)
  have hs : 0 < svarF d L W g i i := by
    rw [svarF_diag d L W g i]
    positivity
  have hN : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by
    have : 0 < W * L := Nat.mul_pos (NeZero.pos W) (NeZero.pos L)
    positivity
  unfold Smix
  rcases ha.eq_or_lt with h0 | h0
  · have hb' : 0 < b := by linarith
    rw [← h0]
    have := div_pos hb' hN
    linarith
  · have := mul_pos h0 hs
    have := div_nonneg hb hN.le
    linarith

end MixVarId

/-! ## Part 2.3 The profile hypothesis, the minor identity, measurability of the statistics -/

section MixBridge

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **The profile hypothesis** (RBM2D `:349`): `S` is symmetric, `E|H_{xy}|² = sigRow v x y = S x y`
off the diagonal and the diagonal coordinate has variance `S x x`. -/
structure MixProfOK (v : CoordF d L W → ℝ≥0) (S : Idx d L W → Idx d L W → ℝ) : Prop where
  symm : ∀ x y, S x y = S y x
  off : ∀ x y, x ≠ y → sigRow d L W v x y = S x y
  diag : ∀ x, (v (x, x, true) : ℝ) = S x x

/-- The mixture variances and the profile `Smix` satisfy the profile hypothesis. -/
theorem mixProfOK (g : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    MixProfOK (mixVar d L W g a b) (Smix d L W g a b) :=
  ⟨Smix_symm d L W g a b, fun _ _ hxy => mixEntry_sigRow_mixVar d L W g ha hb hxy.symm,
    mixEntry_mixVar_diag d L W g ha hb⟩

/-- **The minor resolvent is `greenMinor`**: for Hermitian `H` and `Im z ≠ 0`,
`(H^{(i)} - z)⁻¹_{kl} = G_{kl} - G_{ki} G_{il} / G_{ii}`, i.e. (4.9) via the merged
`inv_minor_resolvent`. -/
theorem mixEntry_minor_eq {ν : Type*} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (i : ν) (k l : {a : ν // a ≠ i}) :
    green (H.submatrix Subtype.val Subtype.val) z k l = greenMinor (green H z) i k.1 l.1 := by
  have hdet : IsUnit (H - z • (1 : Matrix ν ν ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz)
  have h := inv_minor_resolvent hdet i (green_diag_ne_zero hH hz i)
  change ((H.submatrix Subtype.val Subtype.val -
    z • (1 : Matrix {a : ν // a ≠ i} {a : ν // a ≠ i} ℂ))⁻¹ : Matrix {a : ν // a ≠ i}
      {a : ν // a ≠ i} ℂ) k l = _
  rw [h]
  rfl

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`
(through `RBM.Ind.Gres_eq_green_zSig`). -/
private theorem EntryTail_Gres_true {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (z : ℂ) : Gres H z true = green H z := by
  rw [RBM.Ind.Gres_eq_green_zSig]
  rfl

theorem mixEntry_meas_Xmat (k l : Idx d L W) : Measurable fun s : Ω d L W => Xmat d L W s k l :=
  measurable_Xentry d L W k l

theorem mixEntry_meas_green {z : ℂ} (hz : z.im ≠ 0) (k l : Idx d L W) :
    Measurable fun s : Ω d L W => green (Xmat d L W s) z k l := by
  have h := continuous_green_of_isHermitian (continuous_Xmat d L W) (Xmat_isHermitian d L W) hz
  simp only [EntryTail_Gres_true] at h
  exact (h.matrix_elem k l).measurable

theorem mixEntry_meas_greenMinor {z : ℂ} (hz : z.im ≠ 0) (i k l : Idx d L W) :
    Measurable fun s : Ω d L W => greenMinor (green (Xmat d L W s) z) i k l := by
  unfold greenMinor
  exact (mixEntry_meas_green hz k l).sub
    (((mixEntry_meas_green hz k i).mul (mixEntry_meas_green hz i l)).div
      (mixEntry_meas_green hz i i))

theorem mixEntry_meas_ldeRowLHS {z : ℂ} (hz : z.im ≠ 0) (i j : Idx d L W) :
    Measurable fun s : Ω d L W => ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) i j := by
  unfold ldeRowLHS
  exact (Finset.measurable_sum _ fun k _ =>
    (mixEntry_meas_Xmat i k).mul (mixEntry_meas_greenMinor hz i k j)).norm.pow_const 2

theorem mixEntry_meas_ldeRowRHS (S : Idx d L W → Idx d L W → ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i j : Idx d L W) :
    Measurable fun s : Ω d L W => ldeRowRHS S (green (Xmat d L W s) z) i j := by
  unfold ldeRowRHS
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((mixEntry_meas_greenMinor hz i k j).norm.pow_const 2)

theorem mixEntry_meas_ldeColLHS {z : ℂ} (hz : z.im ≠ 0) (k j : Idx d L W) :
    Measurable fun s : Ω d L W => ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) k j := by
  unfold ldeColLHS
  exact (Finset.measurable_sum _ fun l _ =>
    (mixEntry_meas_greenMinor hz j k l).mul (mixEntry_meas_Xmat l j)).norm.pow_const 2

theorem mixEntry_meas_ldeColRHS (S : Idx d L W → Idx d L W → ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (k j : Idx d L W) :
    Measurable fun s : Ω d L W => ldeColRHS S (green (Xmat d L W s) z) k j := by
  unfold ldeColRHS
  exact Finset.measurable_sum _ fun l _ =>
    ((mixEntry_meas_greenMinor hz j k l).norm.pow_const 2).mul measurable_const

theorem mixEntry_meas_ldeQuadLHS (S : Idx d L W → Idx d L W → ℝ) (t : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) :
    Measurable fun s : Ω d L W => ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) S t i := by
  unfold ldeQuadLHS
  refine ((Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
    ((mixEntry_meas_Xmat i k).mul (mixEntry_meas_greenMinor hz i k l)).mul
      (mixEntry_meas_Xmat l i)).sub
    (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      measurable_const.mul (mixEntry_meas_greenMinor hz i k k)))).norm.pow_const 2

theorem mixEntry_meas_ldeQuadRHS (S : Idx d L W → Idx d L W → ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) :
    Measurable fun s : Ω d L W => ldeQuadRHS S (green (Xmat d L W s) z) i := by
  unfold ldeQuadRHS
  exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ =>
    (measurable_const.mul ((mixEntry_meas_greenMinor hz i k l).norm.pow_const 2)).mul
      measurable_const

theorem mixEntry_meas_diag (i : Idx d L W) :
    Measurable fun s : Ω d L W => ‖Xmat d L W s i i‖ ^ 2 :=
  (mixEntry_meas_Xmat i i).norm.pow_const 2

end MixBridge

/-! ## Part 2.4 The four large-deviation tails under `gaussLaw v`

Port of RBM1D `gueEntry_quad_tail` (:1758), `gueEntry_row_tail` (:1775), `gueEntry_col_tail` (:1821),
`gueEntry_diag_tail` (:1878) onto the auxiliary carrier of `AuxCarrier.lean` (RBM2D `:439-733`): the
event is a function of `Xmat s` only, `gaussLaw v` is the push-forward of `seqP (auxSizes d)` by the
rescaled sample `auxT v` (`auxT_law`), and the tails are `aux_lin_tail` (row, column) and
`gaussLaw_quad_tail` at `A = 0` (quadratic form). -/

section MixTails

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **Quadratic LDE (4.7) for the resolvent `G` of `Xmat s`** (RBM1D `gueEntry_quad_tail`, :1758):
`P(λ ∑_{k,l≠i} S_{ik} |G^{(i)}_{kl}|² S_{li} < |Q_i - ∑_k S_{ik} G^{(i)}_{kk}|²) ≤ A_q / λ^{q+1}`. -/
theorem mixEntry_quad_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ}
    (hv : TagFree d L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) (i : Idx d L W) {lam : ℝ}
    (hlam : 0 < lam) (q : ℕ) :
    gaussLaw d L W v {s | lam * ldeQuadRHS S (green (Xmat d L W s) z) i <
        ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) S 1 i}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1)) := by
  have h := gaussLaw_quad_tail hv (A := 0) Matrix.isHermitian_zero hz i hlam q
  have hset : {s : Ω d L W | lam * ldeQuadRHS S (green (Xmat d L W s) z) i <
        ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) S 1 i}
      = {s : Ω d L W | lam * quadVqS d L W v 0 z i s < ‖quadQS d L W v 0 z i s‖ ^ 2} := by
    ext s
    simp only [Set.mem_ofPred_eq]
    have hVq : ldeQuadRHS S (green (Xmat d L W s) z) i = quadVqS d L W v 0 z i s := by
      unfold ldeQuadRHS quadVqS
      simp only [zero_add]
      rw [RowChaos.sum_erase_eq (i := i)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RowChaos.sum_erase_eq (i := i)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mixEntry_minor_eq (Xmat_isHermitian d L W s) hz i k l, ← hS.off i k.1 (Ne.symm k.2),
        hS.symm l.1 i, ← hS.off i l.1 (Ne.symm l.2)]
    have hQ : ldeQuadLHS (Xmat d L W s) (green (Xmat d L W s) z) S 1 i =
        ‖quadQS d L W v 0 z i s‖ ^ 2 := by
      unfold ldeQuadLHS quadQS
      simp only [zero_add]
      congr 2
      rw [RowChaos.sum_erase_eq (i := i)]
      · congr 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [RowChaos.sum_erase_eq (i := i)]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← mixEntry_minor_eq (Xmat_isHermitian d L W s) hz i k l]
        · rw [RowChaos.sum_erase_eq (i := i), Complex.ofReal_one, one_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← mixEntry_minor_eq (Xmat_isHermitian d L W s) hz i k k, ← hS.off i k.1 (Ne.symm k.2)]
    rw [hVq, hQ]
  rw [hset]
  exact h

end MixTails

section MixLinTails

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The minor resolvent of the auxiliary matrix at the shift `A = 0` is `greenMinor` of the resolvent. -/
private theorem mixEntry_auxMinorRes_zero (v : CoordF d L W → ℝ≥0) {z : ℂ} (hz : z.im ≠ 0)
    (i : Idx d L W) (ω : Sizes.SeqΩ (auxSizes d)) (k l : {a : Idx d L W // a ≠ i}) :
    auxMinorRes d L W v 0 z i ω k l = greenMinor (green (auxHG d L W v ω) z) i k.1 l.1 := by
  rw [← mixEntry_minor_eq (auxHG_isHermitian d L W v ω) hz i k l]
  simp [auxMinorRes]

/-- **Row LDE (4.8) for the resolvent `G` of `Xmat s`** (RBM1D `gueEntry_row_tail`, :1775):
`P(Λ ∑_{k≠i} S_{ik} |G^{(i)}_{kj}|² < |∑_{k≠i} H_{ik} G^{(i)}_{kj}|²) ≤ A_q / ((Λ-1)²)^{q+1}` for
`i ≠ j`, `Λ > 1`: the rank-one chaos `auxLinChaos` with the coefficient vector `c_k = G^{(i)}_{kj}`
(which does not read the row `i`). -/
theorem mixEntry_row_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ}
    (hv : TagFree d L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) {i j : Idx d L W}
    (hij : i ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    gaussLaw d L W v {s | Λ * ldeRowRHS S (green (Xmat d L W s) z) i j <
        ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) i j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  obtain ⟨j', rfl⟩ : ∃ j' : {a : Idx d L W // a ≠ i}, j'.1 = j := ⟨⟨j, Ne.symm hij⟩, rfl⟩
  set c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ i} → ℂ :=
    fun ω k => auxMinorRes d L W v 0 z i ω k j' with hc_def
  have hc : ∀ k, Continuous fun ω => c ω k := fun k =>
    continuous_auxMinorRes d L W v Matrix.isHermitian_zero hz i k j'
  have hCb : ∀ ω k, ‖c ω k‖ ≤ |z.im|⁻¹ := fun ω k =>
    norm_auxMinorRes_le d L W v Matrix.isHermitian_zero hz i ω k j'
  have hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W i, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h
    funext k
    simp only [c]
    rw [auxMinorRes_congr d L W v 0 z i h]
  have hc0 : ∀ ω k, c ω k = greenMinor (green (auxHG d L W v ω) z) i k.1 j'.1 :=
    fun ω k => mixEntry_auxMinorRes_zero v hz i ω k j'
  have hY : ∀ ω, ldeRowLHS (Xmat d L W (auxT d L W v ω)) (green (Xmat d L W (auxT d L W v ω)) z) i j'.1
      = ‖∑ k : {a : Idx d L W // a ≠ i}, auxHG d L W v ω i k.1 * c ω k‖ ^ 2 := by
    intro ω
    change ldeRowLHS (auxHG d L W v ω) (green (auxHG d L W v ω) z) i j'.1 = _
    unfold ldeRowLHS
    rw [RowChaos.sum_erase_eq (i := i)]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc0]
  have hR : ∀ ω, ldeRowRHS S (green (Xmat d L W (auxT d L W v ω)) z) i j'.1
      = ∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    change ldeRowRHS S (green (auxHG d L W v ω) z) i j'.1 = _
    unfold ldeRowRHS
    rw [RowChaos.sum_erase_eq (i := i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hS.off i k.1 (Ne.symm k.2), hc0]
  have hR0 : ∀ ω, 0 ≤ ∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2 := by
    intro ω
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by unfold sigRow; positivity) (sq_nonneg _)
  have h := aux_lin_tail (auxLinChaos d L W v i c hc _ hCb hcf)
    (fun ω => ‖∑ k : {a : Idx d L W // a ≠ i}, auxHG d L W v ω i k.1 * c ω k‖ ^ 2)
    (fun ω => ∑ k : {a : Idx d L W // a ≠ i}, sigRow d L W v i k.1 * ‖c ω k‖ ^ 2) hR0
    (fun ω => auxLin_chaos hv i c hc _ hCb hcf ω)
    (fun ω => auxLin_Vq i c hc _ hCb hcf ω) hΛ q
  have hA : MeasurableSet {s : Ω d L W | Λ * ldeRowRHS S (green (Xmat d L W s) z) i j'.1 <
      ldeRowLHS (Xmat d L W s) (green (Xmat d L W s) z) i j'.1} :=
    measurableSet_lt ((mixEntry_meas_ldeRowRHS S hz i j'.1).const_mul Λ)
      (mixEntry_meas_ldeRowLHS hz i j'.1)
  have hmap : gaussLaw d L W v = (Sizes.seqP (auxSizes d)).map (auxT d L W v) :=
    (auxT_law d L W v).symm
  rw [hmap, Measure.map_apply (auxT_measurable d L W v) hA]
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hY ω, hR ω]

/-- **Column LDE (4.8) for the resolvent `G` of `Xmat s`** (RBM1D `gueEntry_col_tail`, :1821):
for `k ≠ j`, the row `j` of `H` against the conjugated minor row `conj G^{(j)}_{k·}`. -/
theorem mixEntry_col_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ}
    (hv : TagFree d L W v) (hS : MixProfOK v S) {z : ℂ} (hz : z.im ≠ 0) {k j : Idx d L W}
    (hkj : k ≠ j) {Λ : ℝ} (hΛ : 1 < Λ) (q : ℕ) :
    gaussLaw d L W v {s | Λ * ldeColRHS S (green (Xmat d L W s) z) k j <
        ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) k j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k' : {a : Idx d L W // a ≠ j}, k'.1 = k := ⟨⟨k, hkj⟩, rfl⟩
  set c : Sizes.SeqΩ (auxSizes d) → {a : Idx d L W // a ≠ j} → ℂ :=
    fun ω l => (starRingEnd ℂ) (auxMinorRes d L W v 0 z j ω k' l) with hc_def
  have hc : ∀ l, Continuous fun ω => c ω l := fun l =>
    Complex.continuous_conj.comp
      (continuous_auxMinorRes d L W v Matrix.isHermitian_zero hz j k' l)
  have hCb : ∀ ω l, ‖c ω l‖ ≤ |z.im|⁻¹ := fun ω l => by
    simp only [c, Complex.norm_conj]
    exact norm_auxMinorRes_le d L W v Matrix.isHermitian_zero hz j ω k' l
  have hcf : ∀ ω ω', (∀ x ∈ auxOffRow d L W j, ω x = ω' x) → c ω = c ω' := by
    intro ω ω' h
    funext l
    simp only [c]
    rw [auxMinorRes_congr d L W v 0 z j h]
  have hc0 : ∀ ω l, c ω l = (starRingEnd ℂ) (greenMinor (green (auxHG d L W v ω) z) j k'.1 l.1) :=
    fun ω l => congrArg (starRingEnd ℂ) (mixEntry_auxMinorRes_zero v hz j ω k' l)
  have hY : ∀ ω, ldeColLHS (Xmat d L W (auxT d L W v ω)) (green (Xmat d L W (auxT d L W v ω)) z) k'.1 j
      = ‖∑ l : {a : Idx d L W // a ≠ j}, auxHG d L W v ω j l.1 * c ω l‖ ^ 2 := by
    intro ω
    change ldeColLHS (auxHG d L W v ω) (green (auxHG d L W v ω) z) k'.1 j = _
    unfold ldeColLHS
    rw [RowChaos.sum_erase_eq (i := j)]
    have e : ∑ l : {a : Idx d L W // a ≠ j}, greenMinor (green (auxHG d L W v ω) z) j k'.1 l.1 *
          auxHG d L W v ω l.1 j
        = (starRingEnd ℂ) (∑ l : {a : Idx d L W // a ≠ j}, auxHG d L W v ω j l.1 * c ω l) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hH : (starRingEnd ℂ) (auxHG d L W v ω j l.1) = auxHG d L W v ω l.1 j :=
        (auxHG_isHermitian d L W v ω).apply l.1 j
      rw [hc0, map_mul, Complex.conj_conj, hH]
      ring
    rw [e, Complex.norm_conj]
  have hR : ∀ ω, ldeColRHS S (green (Xmat d L W (auxT d L W v ω)) z) k'.1 j
      = ∑ l : {a : Idx d L W // a ≠ j}, sigRow d L W v j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    change ldeColRHS S (green (auxHG d L W v ω) z) k'.1 j = _
    unfold ldeColRHS
    rw [RowChaos.sum_erase_eq (i := j)]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hc' : ‖c ω l‖ = ‖greenMinor (green (auxHG d L W v ω) z) j k'.1 l.1‖ := by
      rw [hc0, Complex.norm_conj]
    rw [hc', hS.symm l.1 j, hS.off j l.1 (Ne.symm l.2)]
    ring
  have hR0 : ∀ ω, 0 ≤ ∑ l : {a : Idx d L W // a ≠ j}, sigRow d L W v j l.1 * ‖c ω l‖ ^ 2 := by
    intro ω
    exact Finset.sum_nonneg fun l _ => mul_nonneg (by unfold sigRow; positivity) (sq_nonneg _)
  have h := aux_lin_tail (auxLinChaos d L W v j c hc _ hCb hcf)
    (fun ω => ‖∑ l : {a : Idx d L W // a ≠ j}, auxHG d L W v ω j l.1 * c ω l‖ ^ 2)
    (fun ω => ∑ l : {a : Idx d L W // a ≠ j}, sigRow d L W v j l.1 * ‖c ω l‖ ^ 2) hR0
    (fun ω => auxLin_chaos hv j c hc _ hCb hcf ω)
    (fun ω => auxLin_Vq j c hc _ hCb hcf ω) hΛ q
  have hA : MeasurableSet {s : Ω d L W | Λ * ldeColRHS S (green (Xmat d L W s) z) k'.1 j <
      ldeColLHS (Xmat d L W s) (green (Xmat d L W s) z) k'.1 j} :=
    measurableSet_lt ((mixEntry_meas_ldeColRHS S hz k'.1 j).const_mul Λ)
      (mixEntry_meas_ldeColLHS hz k'.1 j)
  have hmap : gaussLaw d L W v = (Sizes.seqP (auxSizes d)).map (auxT d L W v) :=
    (auxT_law d L W v).symm
  rw [hmap, Measure.map_apply (auxT_measurable d L W v) hA]
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hY ω, hR ω]

end MixLinTails

section MixDiagTail

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Chernoff bound, upper tail, for a centred real Gaussian (copy of the private
`gaussianReal_ge_le` of `Universality/GUELocalSchur.lean`). -/
private theorem mixEntry_gaussianReal_ge_le {v : ℝ≥0} {t s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 v).real {x : ℝ | t ≤ x} ≤ Real.exp (-s * t + (v : ℝ) * s ^ 2 / 2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) t hs
    (integrable_exp_mul_gaussianReal s)
  rw [mgf_id_gaussianReal] at h
  simp only [id, zero_mul, zero_add] at h
  rw [← Real.exp_add] at h
  exact h

/-- Chernoff bound, lower tail, for a centred real Gaussian. -/
private theorem mixEntry_gaussianReal_le_le {v : ℝ≥0} {t s : ℝ} (hs : s ≤ 0) :
    (gaussianReal 0 v).real {x : ℝ | x ≤ t} ≤ Real.exp (-s * t + (v : ℝ) * s ^ 2 / 2) := by
  have h := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) t hs
    (integrable_exp_mul_gaussianReal s)
  rw [mgf_id_gaussianReal] at h
  simp only [id, zero_mul, zero_add] at h
  rw [← Real.exp_add] at h
  exact h

/-- The two-sided Gaussian tail `P(|g| > t) ≤ 2 exp(-t²/(2v))`. -/
private theorem mixEntry_gaussianReal_tail {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    gaussianReal 0 v {x : ℝ | t < |x|} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v))) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast pos_iff_ne_zero.2 hv
  have hsub : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t} := by
    intro x hx
    rcases lt_abs.1 (show t < |x| from hx) with h | h
    · exact Or.inl (show t ≤ x from h.le)
    · exact Or.inr (show x ≤ -t by linarith)
  have h1 : gaussianReal 0 v {x : ℝ | t ≤ x} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((mixEntry_gaussianReal_ge_le (t := t) (s := t / v)
      (by positivity)).trans (le_of_eq ?_))
    congr 1
    field_simp
    ring
  have h2 : gaussianReal 0 v {x : ℝ | x ≤ -t} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ((mixEntry_gaussianReal_le_le (t := -t) (s := -(t / v))
      (by have : 0 ≤ t / v := by positivity
          linarith)).trans (le_of_eq ?_))
    congr 1
    field_simp
    ring
  calc gaussianReal 0 v {x : ℝ | t < |x|}
      ≤ gaussianReal 0 v ({x : ℝ | t ≤ x} ∪ {x : ℝ | x ≤ -t}) := measure_mono hsub
    _ ≤ gaussianReal 0 v {x : ℝ | t ≤ x} + gaussianReal 0 v {x : ℝ | x ≤ -t} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) +
          ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * v))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

/-- **The diagonal entry under `gaussLaw v`** (RBM1D `gueEntry_diag_tail`, :1878): `X_{ii}` is the
real coordinate `s (i,i,true)`, a centred Gaussian of variance `S_{ii} > 0`, so
`P(Λ S_{ii} < |X_{ii}|²) ≤ 2 exp(-Λ/2)` (Chernoff). -/
theorem mixEntry_diag_tail {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ}
    (hS : MixProfOK v S) (i : Idx d L W) (hpos : 0 < S i i) {Λ : ℝ} (hΛ : 0 < Λ) :
    gaussLaw d L W v {s | Λ * S i i < ‖Xmat d L W s i i‖ ^ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-Λ / 2)) := by
  have hXd : ∀ s : Ω d L W, Xmat d L W s i i = ((s (i, i, true) : ℝ) : ℂ) := fun s => by
    simp [Xmat, Xentry]
  have hvd : (v (i, i, true) : ℝ) = S i i := hS.diag i
  have hvne : v (i, i, true) ≠ 0 := by
    intro h
    rw [h, NNReal.coe_zero] at hvd
    linarith
  have ht : 0 < Real.sqrt (Λ * S i i) := Real.sqrt_pos.2 (mul_pos hΛ hpos)
  have hmeas : MeasurableSet {x : ℝ | Real.sqrt (Λ * S i i) < |x|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have hiff : ∀ x : ℝ, (Real.sqrt (Λ * S i i) < |x|) ↔ Λ * S i i < x ^ 2 := by
    intro x
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt_sqrt_iff (mul_pos hΛ hpos).le]
  have hset : {s : Ω d L W | Λ * S i i < ‖Xmat d L W s i i‖ ^ 2} =
      (fun s : Ω d L W => s (i, i, true)) ⁻¹' {x : ℝ | Real.sqrt (Λ * S i i) < |x|} := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hXd, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    rw [hiff]
  have hmeasf : Measurable (fun s : Ω d L W => s (i, i, true)) := measurable_pi_apply _
  have hmap : (gaussLaw d L W v).map (fun s : Ω d L W => s (i, i, true)) =
      gaussianReal 0 (v (i, i, true)) := Measure.infinitePi_map_eval _ _
  rw [hset, ← Measure.map_apply hmeasf hmeas, hmap]
  refine (mixEntry_gaussianReal_tail hvne ht).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  congr 2
  rw [Real.sq_sqrt (mul_pos hΛ hpos).le, hvd]
  field_simp

end MixDiagTail

/-! ## Part 2.5 From the fine-lattice inputs to `mix_det` (block relabelling, `splitEquiv`)

The four large-deviation inputs of `mix_det` are stated on `Vtx d L W` for `blockMat d L W M` and
`greenBlk d L W E u M true`; the tails above are stated on `Idx d L W` for `M` and `green M z`.  The two
are related by the relabelling `(splitEquiv d L W).symm : Vtx d L W ≃ Idx d L W`. -/

section MixRelabel

variable {ν μ : Type*} [Fintype ν] [DecidableEq ν] [Fintype μ] [DecidableEq μ] (f : ν ≃ μ)

private theorem mixEntry_erase_iff (x k : ν) :
    k ∈ (Finset.univ : Finset ν).erase x ↔ f k ∈ (Finset.univ : Finset μ).erase (f x) := by
  simp [Finset.mem_erase, f.injective.eq_iff]

theorem mixEntry_relabel_ldeRowLHS (H G : Matrix μ μ ℂ) (x y : ν) :
    ldeRowLHS (H.submatrix f f) (G.submatrix f f) x y = ldeRowLHS H G (f x) (f y) := by
  unfold ldeRowLHS
  congr 2
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeRowRHS (S : μ → μ → ℝ) (G : Matrix μ μ ℂ) (x y : ν) :
    ldeRowRHS (fun a b => S (f a) (f b)) (G.submatrix f f) x y = ldeRowRHS S G (f x) (f y) := by
  unfold ldeRowRHS
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeColLHS (H G : Matrix μ μ ℂ) (x y : ν) :
    ldeColLHS (H.submatrix f f) (G.submatrix f f) x y = ldeColLHS H G (f x) (f y) := by
  unfold ldeColLHS
  congr 2
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f y k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeColRHS (S : μ → μ → ℝ) (G : Matrix μ μ ℂ) (x y : ν) :
    ldeColRHS (fun a b => S (f a) (f b)) (G.submatrix f f) x y = ldeColRHS S G (f x) (f y) := by
  unfold ldeColRHS
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f y k) (fun k _ => rfl)

theorem mixEntry_relabel_ldeQuadLHS (H G : Matrix μ μ ℂ) (S : μ → μ → ℝ) (t : ℝ) (x : ν) :
    ldeQuadLHS (H.submatrix f f) (G.submatrix f f) (fun a b => S (f a) (f b)) t x
      = ldeQuadLHS H G S t (f x) := by
  unfold ldeQuadLHS
  have h1 : ∑ k ∈ Finset.univ.erase x, ∑ l ∈ Finset.univ.erase x,
        (H.submatrix f f) x k * greenMinor (G.submatrix f f) x k l * (H.submatrix f f) l x
      = ∑ k ∈ Finset.univ.erase (f x), ∑ l ∈ Finset.univ.erase (f x),
        H (f x) k * greenMinor G (f x) k l * H l (f x) :=
    Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ =>
      Finset.sum_equiv f (fun l => mixEntry_erase_iff f x l) (fun l _ => rfl))
  have h2 : ∑ k ∈ Finset.univ.erase x, (S (f x) (f k) : ℂ) * greenMinor (G.submatrix f f) x k k
      = ∑ k ∈ Finset.univ.erase (f x), (S (f x) k : ℂ) * greenMinor G (f x) k k :=
    Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ => rfl)
  rw [h1, h2]

theorem mixEntry_relabel_ldeQuadRHS (S : μ → μ → ℝ) (G : Matrix μ μ ℂ) (x : ν) :
    ldeQuadRHS (fun a b => S (f a) (f b)) (G.submatrix f f) x = ldeQuadRHS S G (f x) := by
  unfold ldeQuadRHS
  exact Finset.sum_equiv f (fun k => mixEntry_erase_iff f x k) (fun k _ =>
    Finset.sum_equiv f (fun l => mixEntry_erase_iff f x l) (fun l _ => rfl))

end MixRelabel

section MixDetBridge

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `greenBlk d L W E u M true` is the fine-lattice resolvent relabelled by `splitEquiv` (the identity
inside the proof of the merged `entryDom_goodEvent_of_llErr`, `Green/EntryDom.lean:289`). -/
theorem mixEntry_greenBlk_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    greenBlk d L W E u M true
      = (green M (zt E u)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold greenBlk Gres blockMat green
  simp only [ite_true]
  have e1 : M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
      zt E u • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix
        (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_submatrix_equiv]

/-- **The deterministic step on the fine lattice**: the four large-deviation inputs of
`mix_det` for `M`, `G = (M - z)⁻¹`, `z = z_{a+b}^{(E)}`, stated on `Idx` (the form of the tails
`mixEntry_*_tail`), give `|(G - m)_{ij}|² ≤ mixCdet d Λ κ Φ² maxLoopPM` for `llErrMat` on the a priori
event `‖G - m‖_max ≤ δ ≤ mixDelta d Λ κ`.  RBM2D `:827`; `hd : 3 ≤ d`, `0 < g ≤ Λ` go to `mix_det`. -/
theorem mixEntry_det (hd : 3 ≤ d) (hL : 3 ≤ L) {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) {g Λ κ E a b : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < a + b)
    (hu1 : a + b < 1) {δ Φ : ℝ} (hllErr : ∀ x y, llErrMat d L W E (a + b) M x y ≤ δ)
    (hδ : δ ≤ mixDelta d Λ κ) (hΦ1 : 1 ≤ Φ) (hΦδ : 36 * Φ * δ ^ 2 ≤ 1)
    (hrow : ∀ i j, i ≠ j → ldeRowLHS M (green M (zt E (a + b))) i j ≤
      Φ * ldeRowRHS (Smix d L W g a b) (green M (zt E (a + b))) i j)
    (hcol : ∀ k j, k ≠ j → ldeColLHS M (green M (zt E (a + b))) k j ≤
      Φ * ldeColRHS (Smix d L W g a b) (green M (zt E (a + b))) k j)
    (hquad : ∀ i, ldeQuadLHS M (green M (zt E (a + b))) (Smix d L W g a b) 1 i ≤
      Φ * ldeQuadRHS (Smix d L W g a b) (green M (zt E (a + b))) i)
    (hdiag : ∀ i, ‖M i i‖ ^ 2 ≤ Φ * Smix d L W g a b i i) (i j : Idx d L W) :
    llErrMat d L W E (a + b) M i j ^ 2 ≤ mixCdet d Λ κ * Φ ^ 2 * maxLoopPM d L W E (a + b) M := by
  have hG := mixEntry_greenBlk_eq (d := d) (L := L) (W := W) E (a + b) M
  have hΩ := entryDom_goodEvent_of_llErr d L W E (a + b) δ M hllErr
  have key := mix_det hd hL hM hg hgΛ hκ hE ha hb hu hu1 hΩ hδ hΦ1 hΦδ
    (fun x y hxy => by
      rw [hG]
      change ldeRowLHS (M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm) _ x y ≤ _
      rw [mixEntry_relabel_ldeRowLHS, mixEntry_relabel_ldeRowRHS (splitEquiv d L W).symm
        (Smix d L W g a b) (green M (zt E (a + b))) x y]
      exact hrow _ _ (fun h => hxy ((splitEquiv d L W).symm.injective h)))
    (fun x y hxy => by
      rw [hG]
      change ldeColLHS (M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm) _ x y ≤ _
      rw [mixEntry_relabel_ldeColLHS, mixEntry_relabel_ldeColRHS (splitEquiv d L W).symm
        (Smix d L W g a b) (green M (zt E (a + b))) x y]
      exact hcol _ _ (fun h => hxy ((splitEquiv d L W).symm.injective h)))
    (fun x => by
      rw [hG]
      change ldeQuadLHS (M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm) _ _ 1 x ≤ _
      rw [mixEntry_relabel_ldeQuadLHS, mixEntry_relabel_ldeQuadRHS (splitEquiv d L W).symm
        (Smix d L W g a b) (green M (zt E (a + b))) x]
      exact hquad _)
    (fun x => hdiag _) ((splitEquiv d L W) i) ((splitEquiv d L W) j)
  have hent : ‖(greenBlk d L W E (a + b) M true - mE E •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) ((splitEquiv d L W) i) ((splitEquiv d L W) j)‖ ^ 2
      = llErrMat d L W E (a + b) M i j ^ 2 := by
    congr 1
    rw [hG]
    unfold llErrMat
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Equiv.symm_apply_apply, (splitEquiv d L W).injective.eq_iff, mul_ite, mul_one,
      mul_zero]
    rw [EntryTail_Gres_true]
  rw [← hent]
  exact key

end MixDetBridge

/-! ## Compiled nonempty instances (T2293; CLAUDE.md §4 step 2)

`d = 3`, `L = 3`, `W = 2` (`Idx 3 3 2 = Z_6^3`, `N = (W L)^d = 216`), profile coupling `g = 1`, mixture
`(a, b) = (1/4, 1/4)` (`u = 1/2`), spectral parameter `z = zt 0 (1/2)` (`Im z = 1/2`).  The statements
on the OU carrier (`ouMat_eq_mixMat`, `mixSample_law`, ...) are at the preflight sequence
`SizesInst.sz0` (`n = 0`: `(L, W) = (4, 32)`, `N = 2^21`, `lam = 1/64`).  Every deterministic
hypothesis is discharged by `norm_num`; the sample `ω` is a variable of the carrier.  The `_sharp`
tails (`λ = Λ = 4`, `q = 0`) have bounds `1/2`, `2/9`; the `λ = Λ = 2`, `q = 1` tails have bounds
`≥ 1` (the ticket's data).  `inst_mixEntry_det` keeps `M` and the four large-deviation inputs as
hypotheses (the form the tails feed); `inst_mixEntry_det_full` proves all of them at `M = 0`. -/

namespace EntryTailCheck

open RBM.Gauss.SizesInst

/-- `Im (zt 0 (1/2)) = 1/2`: `(1 - 1/2) · Im m^{(0)} = 1/2 · 1`. -/
theorem inst_zt_im : (zt 0 (1 / 2)).im = 1 / 2 := by
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [zt_im, mE_im, h4]
  norm_num

theorem inst_zt_im_ne : (zt 0 (1 / 2)).im ≠ 0 := by
  rw [inst_zt_im]
  norm_num

/-- Two distinct points of `Idx 3 3 2`. -/
theorem inst_x1_ne : (![1, 0, 0] : Idx 3 3 2) ≠ (0 : Idx 3 3 2) := fun h => by
  have := congrFun h 0
  revert this
  decide

theorem inst_mixMat_isHermitian
    (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0)) :
    (mixMat sz0 0 (1 / 4) (1 / 4) ω).IsHermitian :=
  mixMat_isHermitian sz0 0 (1 / 4) (1 / 4) ω

theorem inst_ouMat_eq_mixMat (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0)) :
    ouMat (UNModel.band sz0) 0 1 ω = mixMat sz0 0 (Real.exp (-1)) (1 - Real.exp (-1)) ω :=
  ouMat_eq_mixMat sz0 0 1 ω

theorem inst_mixMat_zero_right (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0)) :
    mixMat sz0 0 (1 / 4) 0 ω = Real.sqrt (1 / 4) • Sizes.seqXmat sz0 0 ω.1 :=
  mixMat_zero_right sz0 0 (1 / 4) ω

theorem inst_mixMat_zero_left (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0)) :
    mixMat sz0 0 0 (1 / 4) ω = Real.sqrt (1 / 4) • Xmat 3 (sz0.L 0) (sz0.W 0) ω.2 :=
  mixMat_zero_left sz0 0 (1 / 4) ω

theorem inst_mixMat_eq_Xmat_mixSample (ω : Sizes.SeqΩ sz0 × Ω 3 (sz0.L 0) (sz0.W 0)) :
    mixMat sz0 0 (1 / 4) (1 / 4) ω = Xmat 3 (sz0.L 0) (sz0.W 0) (mixSample sz0 0 (1 / 4) (1 / 4) ω) :=
  mixMat_eq_Xmat_mixSample sz0 0 (1 / 4) (1 / 4) ω

theorem inst_measurable_mixMat : Measurable (mixMat sz0 0 (1 / 4) (1 / 4)) :=
  measurable_mixMat sz0 0 (1 / 4) (1 / 4)

/-- **The one-time law of the mixture** at the preflight sequence, `n = 0`, `(a, b) = (1/4, 1/4)`. -/
theorem inst_mixSample_law :
    (ouP (UNModel.band sz0) 0).map (mixSample sz0 0 (1 / 4) (1 / 4)) =
      gaussLaw 3 (sz0.L 0) (sz0.W 0)
        (mixVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 4) (1 / 4)) :=
  mixSample_law sz0 0 (by norm_num) (by norm_num)

theorem inst_ouP_mixSample_preimage :
    ouP (UNModel.band sz0) 0 (mixSample sz0 0 (1 / 4) (1 / 4) ⁻¹' Set.univ) =
      gaussLaw 3 (sz0.L 0) (sz0.W 0)
        (mixVar 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 4) (1 / 4)) Set.univ :=
  ouP_mixSample_preimage sz0 0 (by norm_num) (by norm_num) MeasurableSet.univ

theorem inst_mixEntry_mixVar_coe (c : CoordF 3 3 2) :
    (mixVar 3 3 2 1 (1 / 4) (1 / 4) c : ℝ) =
      1 / 4 * (gvarF 3 3 2 1 c : ℝ) + 1 / 4 * (gueVar 3 3 2 c : ℝ) :=
  mixEntry_mixVar_coe 3 3 2 1 (by norm_num) (by norm_num) c

theorem inst_mixEntry_sigRow_gvarF :
    sigRow 3 3 2 (gvarF 3 3 2 1) (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) =
      svarF 3 3 2 1 (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  mixEntry_sigRow_gvarF 3 3 2 1 inst_x1_ne

theorem inst_mixEntry_sigRow_mixVar :
    sigRow 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4)) (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) =
      Smix 3 3 2 1 (1 / 4) (1 / 4) (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  mixEntry_sigRow_mixVar 3 3 2 1 (by norm_num) (by norm_num) inst_x1_ne

theorem inst_mixEntry_mixVar_diag (i : Idx 3 3 2) :
    (mixVar 3 3 2 1 (1 / 4) (1 / 4) (i, i, true) : ℝ) = Smix 3 3 2 1 (1 / 4) (1 / 4) i i :=
  mixEntry_mixVar_diag 3 3 2 1 (by norm_num) (by norm_num) i

theorem inst_mixEntry_Smix_diag_pos (i : Idx 3 3 2) : 0 < Smix 3 3 2 1 (1 / 4) (1 / 4) i i :=
  mixEntry_Smix_diag_pos 3 3 2 1 (by norm_num) (by norm_num) (by norm_num) i

theorem inst_mixProfOK :
    MixProfOK (mixVar 3 3 2 1 (1 / 4) (1 / 4)) (Smix 3 3 2 1 (1 / 4) (1 / 4)) :=
  mixProfOK (d := 3) (L := 3) (W := 2) 1 (by norm_num) (by norm_num)

/-- **Quadratic tail** at `v = mixVar 3 3 2 1 (1/4) (1/4)`, `S = Smix …`, row `0`, `λ = 2`, `q = 1`. -/
theorem inst_mixEntry_quad_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
      {s | 2 * ldeQuadRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (0 : Idx 3 3 2) <
        ldeQuadLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (Smix 3 3 2 1 (1 / 4) (1 / 4)) 1 0}
      ≤ ENNReal.ofReal (hwConst 1 / 2 ^ (1 + 1)) :=
  mixEntry_quad_tail (mixVar_tagFree 3 3 2 1 (1 / 4) (1 / 4)) inst_mixProfOK inst_zt_im_ne 0
    (by norm_num) 1

/-- **Row tail**, rows `0 ≠ (1, 0, 0)`, `Λ = 2`, `q = 1`. -/
theorem inst_mixEntry_row_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
      {s | 2 * ldeRowRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) <
        ldeRowLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) 0 (![1, 0, 0] : Idx 3 3 2)}
      ≤ ENNReal.ofReal (hwConst 1 / ((2 - 1) ^ 2) ^ (1 + 1)) :=
  mixEntry_row_tail (mixVar_tagFree 3 3 2 1 (1 / 4) (1 / 4)) inst_mixProfOK inst_zt_im_ne
    inst_x1_ne.symm (by norm_num) 1

/-- **Column tail**, `k = (1, 0, 0) ≠ j = 0`, `Λ = 2`, `q = 1`. -/
theorem inst_mixEntry_col_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
      {s | 2 * ldeColRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (![1, 0, 0] : Idx 3 3 2) (0 : Idx 3 3 2) <
        ldeColLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (![1, 0, 0] : Idx 3 3 2) 0}
      ≤ ENNReal.ofReal (hwConst 1 / ((2 - 1) ^ 2) ^ (1 + 1)) :=
  mixEntry_col_tail (mixVar_tagFree 3 3 2 1 (1 / 4) (1 / 4)) inst_mixProfOK inst_zt_im_ne
    inst_x1_ne (by norm_num) 1

/-- **Diagonal tail**, entry `(0, 0)`, `Λ = 2` (bound `2 exp(-1) ≈ 0.736 < 1`). -/
theorem inst_mixEntry_diag_tail :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
      {s | 2 * Smix 3 3 2 1 (1 / 4) (1 / 4) (0 : Idx 3 3 2) 0 < ‖Xmat 3 3 2 s 0 0‖ ^ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 / 2)) :=
  mixEntry_diag_tail inst_mixProfOK 0 (inst_mixEntry_Smix_diag_pos 0) (by norm_num)

/-- **Quadratic tail with a nontrivial bound**: `λ = 4`, `q = 0` (bound `hwConst 0 / 4 = 1/2`). -/
theorem inst_mixEntry_quad_tail_sharp :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
      {s | 4 * ldeQuadRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (0 : Idx 3 3 2) <
        ldeQuadLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (Smix 3 3 2 1 (1 / 4) (1 / 4)) 1 0}
      ≤ ENNReal.ofReal (hwConst 0 / 4 ^ (0 + 1)) :=
  mixEntry_quad_tail (mixVar_tagFree 3 3 2 1 (1 / 4) (1 / 4)) inst_mixProfOK inst_zt_im_ne 0
    (by norm_num) 0

/-- **Row tail with a nontrivial bound**: `Λ = 4`, `q = 0` (bound `hwConst 0 / 9 = 2/9`). -/
theorem inst_mixEntry_row_tail_sharp :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
      {s | 4 * ldeRowRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) <
        ldeRowLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) 0 (![1, 0, 0] : Idx 3 3 2)}
      ≤ ENNReal.ofReal (hwConst 0 / ((4 - 1) ^ 2) ^ (0 + 1)) :=
  mixEntry_row_tail (mixVar_tagFree 3 3 2 1 (1 / 4) (1 / 4)) inst_mixProfOK inst_zt_im_ne
    inst_x1_ne.symm (by norm_num) 0

/-- **Column tail with a nontrivial bound**: `Λ = 4`, `q = 0`. -/
theorem inst_mixEntry_col_tail_sharp :
    gaussLaw 3 3 2 (mixVar 3 3 2 1 (1 / 4) (1 / 4))
      {s | 4 * ldeColRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
          (![1, 0, 0] : Idx 3 3 2) (0 : Idx 3 3 2) <
        ldeColLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (![1, 0, 0] : Idx 3 3 2) 0}
      ≤ ENNReal.ofReal (hwConst 0 / ((4 - 1) ^ 2) ^ (0 + 1)) :=
  mixEntry_col_tail (mixVar_tagFree 3 3 2 1 (1 / 4) (1 / 4)) inst_mixProfOK inst_zt_im_ne
    inst_x1_ne (by norm_num) 0

/-- `greenBlk` is the relabelled fine-lattice resolvent at `E = 0`, `u = 1/2`, `M = 0`. -/
theorem inst_mixEntry_greenBlk_eq :
    greenBlk 3 3 2 0 (1 / 2) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) true =
      (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (1 / 2))).submatrix
        (splitEquiv 3 3 2).symm (splitEquiv 3 3 2).symm :=
  mixEntry_greenBlk_eq 0 (1 / 2) 0

/-- **The deterministic step** at `d = 3`, `L = 3`, `W = 2`, `g = Λ = κ = 1`, `E = 0`,
`(a, b) = (1/2, 1/4)` (`u = 3/4`), `δ = mixDelta 3 1 1 / 3`, `Φ = 1` (`36 δ² ≤ 1` since
`mixDelta ≤ 1/2`).  `M` is a Hermitian variable and the four large-deviation inputs are hypotheses
(they are the outputs of the tail layer). -/
theorem inst_mixEntry_det {M : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hM : M.IsHermitian)
    (hllErr : ∀ x y, llErrMat 3 3 2 0 (1 / 2 + 1 / 4) M x y ≤ mixDelta 3 1 1 / 3)
    (hrow : ∀ i j, i ≠ j → ldeRowLHS M (green M (zt 0 (1 / 2 + 1 / 4))) i j ≤
      1 * ldeRowRHS (Smix 3 3 2 1 (1 / 2) (1 / 4)) (green M (zt 0 (1 / 2 + 1 / 4))) i j)
    (hcol : ∀ k j, k ≠ j → ldeColLHS M (green M (zt 0 (1 / 2 + 1 / 4))) k j ≤
      1 * ldeColRHS (Smix 3 3 2 1 (1 / 2) (1 / 4)) (green M (zt 0 (1 / 2 + 1 / 4))) k j)
    (hquad : ∀ i, ldeQuadLHS M (green M (zt 0 (1 / 2 + 1 / 4))) (Smix 3 3 2 1 (1 / 2) (1 / 4)) 1 i ≤
      1 * ldeQuadRHS (Smix 3 3 2 1 (1 / 2) (1 / 4)) (green M (zt 0 (1 / 2 + 1 / 4))) i)
    (hdiag : ∀ i, ‖M i i‖ ^ 2 ≤ 1 * Smix 3 3 2 1 (1 / 2) (1 / 4) i i) (i j : Idx 3 3 2) :
    llErrMat 3 3 2 0 (1 / 2 + 1 / 4) M i j ^ 2 ≤
      mixCdet 3 1 1 * 1 ^ 2 * maxLoopPM 3 3 2 0 (1 / 2 + 1 / 4) M := by
  have hpos := mixDelta_pos (κ := 1) (by norm_num) (by norm_num) 3 1
  have hhalf : mixDelta 3 1 1 ≤ 1 / 2 := by
    unfold mixDelta
    exact min_le_left _ _
  exact mixEntry_det (d := 3) (L := 3) (W := 2) (by norm_num) le_rfl hM (g := 1) (Λ := 1)
    (κ := 1) (E := 0) (a := 1 / 2) (b := 1 / 4) one_pos le_rfl one_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hllErr (by linarith) le_rfl
    (by nlinarith) hrow hcol hquad hdiag i j

/-! ### Instances of the index-generic helpers (same data; `f = (splitEquiv 3 3 2).symm : Vtx → Idx`) -/

theorem inst_measurable_mixSample : Measurable (mixSample sz0 0 (1 / 4) (1 / 4)) :=
  measurable_mixSample sz0 0 (1 / 4) (1 / 4)

theorem inst_mixEntry_minor_eq (k l : {a : Idx 3 3 2 // a ≠ 0}) :
    green ((0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix Subtype.val Subtype.val) (zt 0 (1 / 2))
        k l =
      greenMinor (green (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) (zt 0 (1 / 2))) 0 k.1 l.1 :=
  mixEntry_minor_eq Matrix.isHermitian_zero inst_zt_im_ne 0 k l

theorem inst_mixEntry_meas_Xmat :
    Measurable fun s : Ω 3 3 2 => Xmat 3 3 2 s (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  mixEntry_meas_Xmat _ _

theorem inst_mixEntry_meas_green :
    Measurable fun s : Ω 3 3 2 =>
      green (Xmat 3 3 2 s) (zt 0 (1 / 2)) (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  mixEntry_meas_green inst_zt_im_ne _ _

theorem inst_mixEntry_meas_greenMinor :
    Measurable fun s : Ω 3 3 2 => greenMinor (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (0 : Idx 3 3 2)
      (![1, 0, 0] : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  mixEntry_meas_greenMinor inst_zt_im_ne _ _ _

theorem inst_mixEntry_meas_ldeRowLHS :
    Measurable fun s : Ω 3 3 2 => ldeRowLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
      (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  mixEntry_meas_ldeRowLHS inst_zt_im_ne _ _

theorem inst_mixEntry_meas_ldeRowRHS :
    Measurable fun s : Ω 3 3 2 => ldeRowRHS (Smix 3 3 2 1 (1 / 4) (1 / 4))
      (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (0 : Idx 3 3 2) (![1, 0, 0] : Idx 3 3 2) :=
  mixEntry_meas_ldeRowRHS _ inst_zt_im_ne _ _

theorem inst_mixEntry_meas_ldeColLHS :
    Measurable fun s : Ω 3 3 2 => ldeColLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
      (![1, 0, 0] : Idx 3 3 2) (0 : Idx 3 3 2) :=
  mixEntry_meas_ldeColLHS inst_zt_im_ne _ _

theorem inst_mixEntry_meas_ldeColRHS :
    Measurable fun s : Ω 3 3 2 => ldeColRHS (Smix 3 3 2 1 (1 / 4) (1 / 4))
      (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (![1, 0, 0] : Idx 3 3 2) (0 : Idx 3 3 2) :=
  mixEntry_meas_ldeColRHS _ inst_zt_im_ne _ _

theorem inst_mixEntry_meas_ldeQuadLHS :
    Measurable fun s : Ω 3 3 2 => ldeQuadLHS (Xmat 3 3 2 s) (green (Xmat 3 3 2 s) (zt 0 (1 / 2)))
      (Smix 3 3 2 1 (1 / 4) (1 / 4)) 1 (0 : Idx 3 3 2) :=
  mixEntry_meas_ldeQuadLHS _ _ inst_zt_im_ne _

theorem inst_mixEntry_meas_ldeQuadRHS :
    Measurable fun s : Ω 3 3 2 => ldeQuadRHS (Smix 3 3 2 1 (1 / 4) (1 / 4))
      (green (Xmat 3 3 2 s) (zt 0 (1 / 2))) (0 : Idx 3 3 2) :=
  mixEntry_meas_ldeQuadRHS _ inst_zt_im_ne _

theorem inst_mixEntry_meas_diag :
    Measurable fun s : Ω 3 3 2 => ‖Xmat 3 3 2 s (0 : Idx 3 3 2) 0‖ ^ 2 :=
  mixEntry_meas_diag _

theorem inst_mixEntry_relabel_ldeRowLHS (x y : Vtx 3 3 2) :
    ldeRowLHS ((0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm)
      ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm) x y =
      ldeRowLHS (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) 1 ((splitEquiv 3 3 2).symm x)
        ((splitEquiv 3 3 2).symm y) :=
  mixEntry_relabel_ldeRowLHS (splitEquiv 3 3 2).symm _ _ x y

theorem inst_mixEntry_relabel_ldeRowRHS (x y : Vtx 3 3 2) :
    ldeRowRHS (fun a b => Smix 3 3 2 1 (1 / 4) (1 / 4) ((splitEquiv 3 3 2).symm a)
        ((splitEquiv 3 3 2).symm b))
      ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm) x y =
      ldeRowRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
        ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y) :=
  mixEntry_relabel_ldeRowRHS (splitEquiv 3 3 2).symm _ _ x y

theorem inst_mixEntry_relabel_ldeColLHS (x y : Vtx 3 3 2) :
    ldeColLHS ((0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm)
      ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm) x y =
      ldeColLHS (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) 1 ((splitEquiv 3 3 2).symm x)
        ((splitEquiv 3 3 2).symm y) :=
  mixEntry_relabel_ldeColLHS (splitEquiv 3 3 2).symm _ _ x y

theorem inst_mixEntry_relabel_ldeColRHS (x y : Vtx 3 3 2) :
    ldeColRHS (fun a b => Smix 3 3 2 1 (1 / 4) (1 / 4) ((splitEquiv 3 3 2).symm a)
        ((splitEquiv 3 3 2).symm b))
      ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm) x y =
      ldeColRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
        ((splitEquiv 3 3 2).symm x) ((splitEquiv 3 3 2).symm y) :=
  mixEntry_relabel_ldeColRHS (splitEquiv 3 3 2).symm _ _ x y

theorem inst_mixEntry_relabel_ldeQuadLHS (x : Vtx 3 3 2) :
    ldeQuadLHS ((0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm)
      ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm)
      (fun a b => Smix 3 3 2 1 (1 / 4) (1 / 4) ((splitEquiv 3 3 2).symm a)
        ((splitEquiv 3 3 2).symm b)) 1 x =
      ldeQuadLHS (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) 1 (Smix 3 3 2 1 (1 / 4) (1 / 4)) 1
        ((splitEquiv 3 3 2).symm x) :=
  mixEntry_relabel_ldeQuadLHS (splitEquiv 3 3 2).symm _ _ _ 1 x

theorem inst_mixEntry_relabel_ldeQuadRHS (x : Vtx 3 3 2) :
    ldeQuadRHS (fun a b => Smix 3 3 2 1 (1 / 4) (1 / 4) ((splitEquiv 3 3 2).symm a)
        ((splitEquiv 3 3 2).symm b))
      ((1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ).submatrix (splitEquiv 3 3 2).symm
        (splitEquiv 3 3 2).symm) x =
      ldeQuadRHS (Smix 3 3 2 1 (1 / 4) (1 / 4)) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
        ((splitEquiv 3 3 2).symm x) :=
  mixEntry_relabel_ldeQuadRHS (splitEquiv 3 3 2).symm _ _ x

/-! ### The deterministic step with every hypothesis discharged (`M = 0`)

At `M = 0`, `E = 0`: `G = (-z)⁻¹ • 1` is a scalar matrix, so `ldeRowLHS = ldeColLHS = 0`,
`ldeQuadLHS = |c|² (∑_{k≠i} S_{ik})²` and `ldeQuadRHS = |c|² ∑_{k≠i} S_{ik}²` (`c = (-z)⁻¹`), and the
quadratic input is Cauchy-Schwarz with the constant `N - 1 = 215 ≤ Φ = 256`.  `‖G - m‖_max = u/(1-u)`.
Nothing is a hypothesis: `δ = min (mixDelta 3 1 1) (1/100)`, `u = δ/(1+δ)`, `(a, b) = (u/2, u/2)`. -/

section ZeroMat

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

theorem inst_green_zero {z : ℂ} (hz : z ≠ 0) :
    green (0 : Matrix ν ν ℂ) z = (-z)⁻¹ • (1 : Matrix ν ν ℂ) := by
  unfold green
  apply Matrix.inv_eq_right_inv
  rw [zero_sub, ← neg_smul, smul_mul_smul_comm, one_mul, mul_inv_cancel₀ (neg_ne_zero.2 hz),
    one_smul]

theorem inst_greenMinor_zero {z : ℂ} (hz : z ≠ 0) {i k l : ν} (hk : k ≠ i) :
    greenMinor (green (0 : Matrix ν ν ℂ) z) i k l = if k = l then (-z)⁻¹ else 0 := by
  rw [inst_green_zero hz]
  simp [greenMinor, Matrix.smul_apply, Matrix.one_apply, hk]

theorem inst_ldeRowLHS_zero (G : Matrix ν ν ℂ) (i j : ν) :
    ldeRowLHS (0 : Matrix ν ν ℂ) G i j = 0 := by
  simp [ldeRowLHS]

theorem inst_ldeColLHS_zero (G : Matrix ν ν ℂ) (k j : ν) :
    ldeColLHS (0 : Matrix ν ν ℂ) G k j = 0 := by
  simp [ldeColLHS]

theorem inst_ldeQuadLHS_zero {z : ℂ} (hz : z ≠ 0) (S : ν → ν → ℝ) (i : ν) :
    ldeQuadLHS (0 : Matrix ν ν ℂ) (green 0 z) S 1 i =
      ‖(-z)⁻¹‖ ^ 2 * (∑ k ∈ Finset.univ.erase i, S i k) ^ 2 := by
  unfold ldeQuadLHS
  have h : ∑ k ∈ Finset.univ.erase i, (S i k : ℂ) * greenMinor (green (0 : Matrix ν ν ℂ) z) i k k =
      (((∑ k ∈ Finset.univ.erase i, S i k : ℝ) : ℂ)) * (-z)⁻¹ := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [inst_greenMinor_zero hz (Finset.ne_of_mem_erase hk)]
    simp
  rw [h]
  simp only [Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero, Complex.ofReal_one,
    one_mul, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

theorem inst_ldeQuadRHS_zero {z : ℂ} (hz : z ≠ 0) (S : ν → ν → ℝ) (hS : ∀ x y, S x y = S y x)
    (i : ν) :
    ldeQuadRHS S (green (0 : Matrix ν ν ℂ) z) i =
      ‖(-z)⁻¹‖ ^ 2 * ∑ k ∈ Finset.univ.erase i, S i k ^ 2 := by
  unfold ldeQuadRHS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≠ i := Finset.ne_of_mem_erase hk
  rw [Finset.sum_eq_single k]
  · have hkk : (if k = k then (-z)⁻¹ else 0) = (-z)⁻¹ := by simp
    rw [inst_greenMinor_zero hz hk', hkk, hS k i]
    ring
  · intro l _ hlk
    have hkl : (if k = l then (-z)⁻¹ else 0) = 0 := by simp [Ne.symm hlk]
    rw [inst_greenMinor_zero hz hk', hkl]
    simp
  · intro h
    exact absurd hk h

/-- The quadratic input at `M = 0` (Cauchy-Schwarz with `#(univ.erase i) = N - 1`). -/
theorem inst_quad_zero {z : ℂ} (hz : z ≠ 0) (S : ν → ν → ℝ) (hS : ∀ x y, S x y = S y x) (i : ν)
    {Φ : ℝ} (hΦ : ((Fintype.card ν - 1 : ℕ) : ℝ) ≤ Φ) :
    ldeQuadLHS (0 : Matrix ν ν ℂ) (green 0 z) S 1 i ≤
      Φ * ldeQuadRHS S (green (0 : Matrix ν ν ℂ) z) i := by
  rw [inst_ldeQuadLHS_zero hz S i, inst_ldeQuadRHS_zero hz S hS i]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i) (f := fun k => S i k)
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ] at hcs
  have h0 : 0 ≤ ∑ k ∈ Finset.univ.erase i, S i k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h1 : 0 ≤ ‖(-z)⁻¹‖ ^ 2 := sq_nonneg _
  calc ‖(-z)⁻¹‖ ^ 2 * (∑ k ∈ Finset.univ.erase i, S i k) ^ 2
      ≤ ‖(-z)⁻¹‖ ^ 2 * (((Fintype.card ν - 1 : ℕ) : ℝ) * ∑ k ∈ Finset.univ.erase i, S i k ^ 2) :=
        mul_le_mul_of_nonneg_left hcs h1
    _ ≤ ‖(-z)⁻¹‖ ^ 2 * (Φ * ∑ k ∈ Finset.univ.erase i, S i k ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΦ h0) h1
    _ = Φ * (‖(-z)⁻¹‖ ^ 2 * ∑ k ∈ Finset.univ.erase i, S i k ^ 2) := by ring

end ZeroMat

theorem inst_mE_zero : mE 0 = Complex.I := by
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  simp only [mE, h4]
  push_cast
  ring

theorem inst_zt_zero (u : ℝ) : zt 0 u = (((1 - u : ℝ) : ℂ)) * Complex.I := by
  simp [zt, inst_mE_zero]

theorem inst_zt_zero_ne {u : ℝ} (hu1 : u < 1) : zt 0 u ≠ 0 := by
  have h1 : (1 - u : ℝ) ≠ 0 := by linarith
  rw [inst_zt_zero]
  exact mul_ne_zero (by exact_mod_cast h1) Complex.I_ne_zero

/-- `‖G - m‖_max` at `M = 0`, `E = 0`: the diagonal is `u/(1-u)`, the off-diagonal `0`. -/
theorem inst_llErr_zero {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (x y : Idx 3 3 2) :
    llErrMat 3 3 2 0 u (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) x y =
      if x = y then u / (1 - u) else 0 := by
  have h1 : (1 - (u : ℂ)) ≠ 0 := by
    have : (1 - u : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  unfold llErrMat
  rw [EntryTail_Gres_true, inst_green_zero (inst_zt_zero_ne hu1), inst_mE_zero]
  by_cases hxy : x = y
  · subst hxy
    simp only [Matrix.smul_apply, Matrix.one_apply, ite_true, smul_eq_mul, mul_one]
    have : (-zt 0 u)⁻¹ - Complex.I = Complex.I * (((u / (1 - u) : ℝ)) : ℂ) := by
      rw [inst_zt_zero]
      push_cast
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [this, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hu0 (by linarith)), one_mul]
  · simp [Matrix.smul_apply, hxy]

/-- **The deterministic step at `M = 0`**, general `(u, δ)`: every hypothesis of `mixEntry_det` is proved. -/
theorem inst_det_zero {u δ : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hδu : u / (1 - u) ≤ δ)
    (hδc : δ ≤ mixDelta 3 1 1) (hΦδ : 36 * 256 * δ ^ 2 ≤ 1) (i j : Idx 3 3 2) :
    llErrMat 3 3 2 0 (u / 2 + u / 2) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) i j ^ 2 ≤
      mixCdet 3 1 1 * 256 ^ 2 * maxLoopPM 3 3 2 0 (u / 2 + u / 2)
        (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) := by
  have hab : u / 2 + u / 2 = u := by ring
  have hS : ∀ x y : Idx 3 3 2,
      Smix 3 3 2 1 (u / 2) (u / 2) x y = Smix 3 3 2 1 (u / 2) (u / 2) y x :=
    fun x y => Smix_symm 3 3 2 1 (u / 2) (u / 2) x y
  have hcard : ((Fintype.card (Idx 3 3 2) - 1 : ℕ) : ℝ) ≤ 256 := by
    rw [RBM.Gauss.card_Idx]
    norm_num
  have hδ0 : 0 ≤ δ := le_trans (div_nonneg hu0.le (by linarith)) hδu
  refine mixEntry_det (d := 3) (L := 3) (W := 2) (by norm_num) le_rfl Matrix.isHermitian_zero
    (g := 1) (Λ := 1) (κ := 1) (E := 0) (a := u / 2) (b := u / 2) one_pos le_rfl one_pos
    (by norm_num) (by linarith) (by linarith) (by rw [hab]; exact hu0) (by rw [hab]; exact hu1)
    (δ := δ) (Φ := 256) ?_ hδc (by norm_num) hΦδ ?_ ?_ ?_ ?_ i j
  · intro x y
    rw [hab, inst_llErr_zero hu0 hu1]
    split_ifs
    · exact hδu
    · exact hδ0
  · intro i j _
    rw [inst_ldeRowLHS_zero]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => mul_nonneg ?_ (sq_nonneg _))
    exact Smix_nonneg 3 3 2 1 (by linarith) (by linarith) i k
  · intro k j _
    rw [inst_ldeColLHS_zero]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun l _ => mul_nonneg (sq_nonneg _) ?_)
    exact Smix_nonneg 3 3 2 1 (by linarith) (by linarith) l j
  · intro i
    rw [hab]
    exact inst_quad_zero (inst_zt_zero_ne hu1) _ hS i hcard
  · intro i
    rw [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (by norm_num) (Smix_nonneg 3 3 2 1 (by linarith) (by linarith) i i)

/-- The data of the discharged instance: `δ = min (mixDelta 3 1 1) (1/100)` and `u = δ/(1+δ)`. -/
def instDelta : ℝ := min (mixDelta 3 1 1) (1 / 100)

theorem instDelta_pos : 0 < instDelta :=
  lt_min (mixDelta_pos (κ := 1) (by norm_num) (by norm_num) 3 1) (by norm_num)

def instU : ℝ := instDelta / (1 + instDelta)

/-- **The deterministic step with every hypothesis discharged**: `d = 3`, `L = 3`, `W = 2`,
`g = Λ = κ = 1`, `E = 0`, `M = 0`, `Φ = 256`, `δ = instDelta`, `u = instU`, `(a, b) = (u/2, u/2)`;
the four large-deviation inputs and `‖G - m‖_max ≤ δ ≤ mixDelta 3 1 1` are proved, not assumed. -/
theorem inst_mixEntry_det_full (i j : Idx 3 3 2) :
    llErrMat 3 3 2 0 (instU / 2 + instU / 2) (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) i j ^ 2 ≤
      mixCdet 3 1 1 * 256 ^ 2 * maxLoopPM 3 3 2 0 (instU / 2 + instU / 2)
        (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) := by
  have hδ0 := instDelta_pos
  have hδ100 : instDelta ≤ 1 / 100 := min_le_right _ _
  have hu0 : 0 < instU := div_pos hδ0 (by linarith)
  have hu1 : instU < 1 := by
    unfold instU
    rw [div_lt_one (by linarith)]
    linarith
  have hu_eq : instU / (1 - instU) = instDelta := by
    have h1 : 1 - instU = 1 / (1 + instDelta) := by
      unfold instU
      field_simp
      ring
    rw [h1]
    unfold instU
    field_simp
  exact inst_det_zero hu0 hu1 hu_eq.le (min_le_left _ _) (by nlinarith) i j

end EntryTailCheck

end RBM.Univ

end
