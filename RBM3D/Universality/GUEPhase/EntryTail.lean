/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.EntryDet

/-!
# The probabilistic half of Lemma 4.1 at the mixture profile, first half, `d ≥ 3`

The argument follows the first part of the two-dimensional formalization (`GUEPhase/EntryTail` of RBM2D: the
carrier, law, profile and large-deviation-tail layer, and the deterministic bridge) at `d ≥ 3`.  The second half (the
union of the failure events, the size scale and `gueEntryMix`) is `EntryTailMain.lean`.  The equation numbers
(4.2), (4.3), (4.7), (4.8) below are those of Lemma 4.1 of [YY_25].

* the mixture matrix `mixMat sz n a b ω = √a X_band(ω₁) + √b X_GUE(ω₂)` on the band OU carrier
  `ouP (UNModel.band sz) n` (`SeqΩ sz × Ω d (L n) (W n)`, the band coordinates are read through
  `slice sz n`, the coupling is `sz.lam n`), `ouMat_eq_mixMat`, and the statement `GUEEntryMix d`;
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

/-! ## §7 The statement `GUEEntryMix`: Lemma 4.1 for the mixture profile -/

section PinEntry

variable {d : ℕ}

/-- The mixture matrix `√a X_band + √b X_GUE` on the OU carrier `ouP = seqP ⊗ gueP` of the band model:
its entry variance profile is `a S(g) + b N⁻¹` (`Smix`), `g = sz.lam n`.  With `(a, b) = (t₁, u - t₁)`
it is the one-time law of the GUE-phase grid path; with `(a, b) = (e^{-t}, 1 - e^{-t})` it is the OU
marginal `ouMat t` (`ouMat_eq_mixMat`).  As in RBM2D; the band matrix is `seqXmat sz n ω.1`. -/
def mixMat (sz : Sizes d) (n : ℕ) (a b : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Real.sqrt a • Sizes.seqXmat sz n ω.1 + Real.sqrt b • Xmat d (sz.L n) (sz.W n) ω.2

theorem ouMat_eq_mixMat (sz : Sizes d) (n : ℕ) (t : ℝ)
    (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat (UNModel.band sz) n t ω = mixMat sz n (Real.exp (-t)) (1 - Real.exp (-t)) ω := by
  have h : Real.sqrt (Real.exp (-t)) = Real.exp (-t / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _), ← Real.exp_add]
    congr 1; ring
  simp only [ouMat, mixMat, UNModel.band, h]

end PinEntry

/-- **`GUEEntryMix d`**: the output of the probabilistic half of Lemma 4.1 at the mixture profile.
Lemma 4.1 (4.2)+(4.3) of [YY_25] for the profile `S_u = a S(g) + b N⁻¹`,
`u = a + b < 1`, `g = sz.lam n`, at a polynomially large family of mixture parameters
`(a_{n,k}, b_{n,k})`, `k ≤ K_n ≤ N^{n0}`, in the one-time-law form on `ouP (UNModel.band sz) n` (the union
over the grid is inside the probability): on the a priori event `‖G - m‖_max ≤ δ_n`, `δ_n ≤ N^{-c₀}`,
`|G_ij - m δ_ij|² ≺ max_{a,b} |𝓛_{(+,-),(a,b)}| + W^{-d}`, at the energy `E_n` and the spectral parameter
`z_u^{(E)}` with `u = a + b`.  `b = 0` is the band statement, `a = 0` the flat GUE.  Paper: Lemma 3.1
(`lem_GbEXP`), which follows Lemma 4.1 of [YY_25]; it is used in the proof of Theorem 2.4.  Differences from RBM2D:
`W⁻² ↦ W^{-d}`; `Admissible 𝔠 d ↦ sz.Admissible 𝔠 𝔡`; `3 ≤ d` is not part of the statement. -/
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
(RBM2D: the band coordinates are read through `slice sz n`). -/
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

/-- The mixture on the pair space `Ω × Ω` (the pair-space form of `mixSample`; helper). -/
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
`mixSample_law`, with `P` replaced by `PF d L W g`; copy of the private `ouSamplePair_law` of
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

/-- **The one-time Gaussian law of the mixture, for every `a, b ≥ 0`** (RBM2D `mixSample_law`;
the `ouSample_law` is the case `(a, b) = (e^{-t}, 1 - e^{-t})`, `a > 0`, `a + b = 1`, and does
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

/-- `sigRow (gvarF g) i k = S_{ik}` for `k ≠ i` (two real coordinates of variance `S_{ik}/2`);
RBM2D `mixEntry_sigRow_gvar`. -/
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

/-- **The profile hypothesis** (RBM2D): `S` is symmetric, `E|H_{xy}|² = sigRow v x y = S x y`
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
`(H^{(i)} - z)⁻¹_{kl} = G_{kl} - G_{ki} G_{il} / G_{ii}`, i.e. (4.9) via the
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

/-- The `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`
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

Port of RBM1D `gueEntry_quad_tail`, `gueEntry_row_tail`, `gueEntry_col_tail`,
`gueEntry_diag_tail` onto the auxiliary carrier of `AuxCarrier.lean` (RBM2D): the
event is a function of `Xmat s` only, `gaussLaw v` is the push-forward of `seqP (auxSizes d)` by the
rescaled sample `auxT v` (`auxT_law`), and the tails are `aux_lin_tail` (row, column) and
`gaussLaw_quad_tail` at `A = 0` (quadratic form). -/

section MixTails

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **Quadratic LDE (4.7) for the resolvent `G` of `Xmat s`** (RBM1D `gueEntry_quad_tail`):
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

/-- **Row LDE (4.8) for the resolvent `G` of `Xmat s`** (RBM1D `gueEntry_row_tail`):
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

/-- **Column LDE (4.8) for the resolvent `G` of `Xmat s`** (RBM1D `gueEntry_col_tail`):
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
`GUELocalSchur_gaussianReal_ge_le` of `Universality/GUELocalSchur.lean`). -/
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

/-- **The diagonal entry under `gaussLaw v`** (RBM1D `gueEntry_diag_tail`): `X_{ii}` is the
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
inside the proof of the `entryDom_goodEvent_of_llErr`). -/
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
event `‖G - m‖_max ≤ δ ≤ mixDelta d Λ κ`.  As in RBM2D; `hd : 3 ≤ d`, `0 < g ≤ Λ` go to `mix_det`. -/
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


end RBM.Univ

end
