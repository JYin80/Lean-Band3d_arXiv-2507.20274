/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenStab
import RBM3D.BA.Step1Boot

/-!
# The block Anderson local law at a deterministic control, per-sequence layer (BA-G6a)

Ticket T2408 (design gate `docs/reports/T2408-prove.md` (a), (G); the pins GL1-GL6 of (G)(v) and their probe
`RBM3D/Probe/T2408Pins.lean`, which is not merged).  Paper: `paper/tex/7_8_light_weight.tex` (`7_8:line`, `lem_GbEXP_BA`
`:1916-1946`), band `paper/tex/3_5_Loop_Hierarchy.tex`.  The band route of `Green/LocalLaw.lean`
(`AsGMcSeq` + `LoopDetSeq` → `LocalLawDetSeq` → floor → averaged law) read at the block Anderson carrier `baFMz sz z`
and the law `seqP (sz.withLam 0)`; the per-time deterministic cores are the merged `GreenCore_diag` (G3a), `baStab_holds`
(G3b), `baGbEXPij'_holds` (G4, not used here).

* **GL1** `GreenLocal_floor_sample`: one sample, `‖G - M‖_max ≤ κ/2` gives `W^{-d} ≤ (4/κ²) 𝓛^{(2)}_{(-,+),(a,a)}`.
* **GL2** `baGbEXPii_holds`: the pin `BAGbEXPii d` for `2 ≤ d` (`(GiiGEX)`, event form).
* **GL3** `greenLocal_localLaw`: `(initialGT2)` gives `‖G_t - M‖_max ≺ Ψ`.
* **GL4** `greenLocal_floor`: `(initialGT2)` gives `W^{-d} ≤ (4/κ²) N^ν Ψ²` eventually.
* **GL5** `greenLocal_omega`: `‖G_t - M‖_max ≺ W^{-ε₀}` gives the event `{‖G_t - M‖_max ≤ N^ζ W^{-ε₀}}` with high probability.
* **GL6** `greenLocal_gav_of_fa`: the averaged law of `𝒦` gives `‖L^{(1)}_a - m‖ ≺ Ψ²` (`BAGavLGEX`).
* The bridges to G5a, G5c and the wiring lemma of G6b (`greenLocal_gbEXPav_of_fa`).

Every constant depends on `(d, κ, 𝔡)` only (`κ` uniform in `L`); no `g ≤ W^{-ε}`, no smallness of `‖M - m₀ I‖`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section
open MeasureTheory Filter Matrix Finset
open RBM RBM.Green RBM.Gauss RBM.Gauss.Sizes

namespace RBM.BA

/-! ## 0. Vocabulary: the pins GL3-GL6 as `Prop`s -/

/-- **GL3 `GreenLocal_LocalLaw`**: the BA local law at a deterministic control, per sequence: `(initialGT2)`
(`STInitialGT2gL`, `Chain/Carrier.lean:140`) gives `‖G_t - M‖_max ≺ Ψ` (the band `LocalLawDetThm`,
`Green/LocalLaw.lean:166`, with the carrier `baFMz`). -/
def GreenLocal_LocalLaw (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ Ψ n) →
          STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
              (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => Ψ n)

/-- **GL4 `GreenLocal_Floor`**: the BA floor along the flow (the band `LoopFloorThm`, `Green/LocalLaw.lean:207`,
`4 N^ε Ψ²` replaced by `(4/κ²) N^ν Ψ²`; `ν` is the exponent of `N`, `ε` is that of `BAFlow`). -/
def GreenLocal_Floor (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          STInitialGT2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ →
            ∀ ν : ℝ, 0 < ν → ∀ᶠ n in atTop,
              (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 4 / κ ^ 2 * ((sz.size n : ℕ) : ℝ) ^ ν * Ψ n ^ 2

/-- **GL5 `GreenLocal_omega`**: from (A) of `(initialGT2)` (`‖G_t - M‖_max ≺ W^{-ε₀}`) the event
`{‖G_t - M‖_max ≤ N^ζ W^{-ε₀}}` has high probability, and `N^ζ W^{-ε₀} ≤ κ/2` eventually, for `0 < ζ ≤ 𝔠 ε₀ / 2`
(`W ≥ N^𝔠`).  No guard on `d`. -/
def GreenLocal_omega (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          ∀ ζ : ℝ, 0 < ζ → ζ ≤ 𝔠 * ε₀ / 2 →
            (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ ζ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ κ / 2) ∧
            HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size
              (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
                ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ζ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀)})

/-- **GL6 `GreenLocal_Gav`** (the averaged wiring): the averaged law of the residual `𝒦` (the conclusion of `BAFAav`,
owed by G5b) gives `‖L^{(1)}_a - m‖ ≺ Ψ²` uniformly in `a` (the conclusion of `BAGavLGEX`, `BA/Step1Boot.lean:97-103`):
`L^{(1)}_a - m = v̄_a`, `v̄ - t M^{(+,+)} v̄ = ⟨M𝒦⟩` (`GreenCore_E3`), `‖v̄‖_max ≤ 16 κ⁻⁴ ‖⟨M𝒦⟩‖_max` (`baStab_holds`). -/
def GreenLocal_Gav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ Ψ : ℕ → ℝ,
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
          (fun n a ω => ‖(((sz.W n : ℝ) ^ d)⁻¹ : ℝ) * ∑ o, ∑ b',
            BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b' *
              GreenCore_K (GreenCore_Gc sz z n (t n) ω) (GreenCore_Mc sz z n) (GreenCore_Xc sz n (t n) ω)
                (GreenCore_Dc sz z n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (b', o) (a, o)‖)
          (fun n _ _ => Ψ n ^ 2) →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n))
          (fun n a ω => ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz z).m n‖)
          (fun n _ _ => Ψ n ^ 2)

/-! ## 1. GL1: the floor at one sample -/

section Floor

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **GL1 `GreenLocal_floor_sample`** (one sample, deterministic; the BA twin of `inv_Wd_le_maxLoopPM`,
`Green/EntryDom.lean:386`): `|M_{uu}| = |m| ≥ κ` and `‖G - M‖_max ≤ δ ≤ κ/2` give `|G_{uu}| ≥ κ/2`, so
`𝓛^{(2)}_{(-,+),(a,a)} ≥ W^{-d} κ²/4`. -/
theorem GreenLocal_floor_sample {G M : Matrix (Vtx d L W) (Vtx d L W) ℂ} {Mb : Matrix (Zd d L) (Zd d L) ℂ} {m : ℂ}
    {κ δ : ℝ} (hκ : 0 < κ) (hM : ∀ u v, M u v = if u.2 = v.2 then Mb u.1 v.1 else 0) (hMd : ∀ a, Mb a a = m)
    (hκm : κ ≤ ‖m‖) (hδ : δ ≤ κ / 2) (hΩ : ∀ u v, ‖G u v - M u v‖ ≤ δ) (a : Zd d L) :
    ((W : ℝ) ^ d)⁻¹ ≤ 4 / κ ^ 2 * GreenCore_loop G a a := by
  have hw := GreenCore_w_pos (d := d) (W := W)
  have hdiag : ∀ o : Fin (W ^ d), κ / 2 ≤ ‖G (a, o) (a, o)‖ := fun o => by
    have h1 : M (a, o) (a, o) = m := by simp [hM, hMd]
    have h2 := norm_sub_norm_le (M (a, o) (a, o)) (G (a, o) (a, o))
    have h3 := hΩ (a, o) (a, o)
    rw [h1] at h2 h3
    rw [norm_sub_rev] at h2
    linarith
  have hrow : ∀ o : Fin (W ^ d), (κ / 2) ^ 2 ≤ ∑ o' : Fin (W ^ d), ‖G (a, o) (a, o')‖ ^ 2 := fun o =>
    (pow_le_pow_left₀ (by linarith) (hdiag o) 2).trans
      (Finset.single_le_sum (f := fun o' : Fin (W ^ d) => ‖G (a, o) (a, o')‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ o))
  have hsum : ((W ^ d : ℕ) : ℝ) * (κ / 2) ^ 2 ≤ ∑ o : Fin (W ^ d), ∑ o' : Fin (W ^ d), ‖G (a, o) (a, o')‖ ^ 2 := by
    have := Finset.sum_le_sum fun o (_ : o ∈ Finset.univ) => hrow o
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hlo : ((W : ℝ) ^ d)⁻¹ * (κ / 2) ^ 2 ≤ GreenCore_loop G a a := by
    unfold GreenCore_loop
    have e : ((W : ℝ) ^ d)⁻¹ * (κ / 2) ^ 2 = (((W : ℝ) ^ d)⁻¹) ^ 2 * (((W ^ d : ℕ) : ℝ) * (κ / 2) ^ 2) := by
      have hW0 : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
      rw [Nat.cast_pow]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hκ2 : 0 < κ ^ 2 := by positivity
  calc ((W : ℝ) ^ d)⁻¹ = 4 / κ ^ 2 * (((W : ℝ) ^ d)⁻¹ * (κ / 2) ^ 2) := by field_simp; ring
    _ ≤ 4 / κ ^ 2 * GreenCore_loop G a a := mul_le_mul_of_nonneg_left hlo (by positivity)

end Floor

/-! ## 2. Private helpers: events, the carrier link, eventual inequalities -/

section Helpers

/-- `ξ ≺ ζ` from the events `{∀ u, ξ ≤ N^τ ζ}` holding with high probability for every `τ > 0` (the converse of
`StochDomAt.highProb`). -/
private theorem GreenLocal_prec_of_whp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω})) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl
  refine le_trans (le_of_eq ?_) hl
  congr 1
  ext ω
  simp [badSetAt]

private theorem GreenLocal_le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hab
  push Not at hab
  nlinarith

/-- `√(N^{2ζ}) = N^ζ`. -/
private theorem GreenLocal_sqrt_rpow {N : ℝ} (hN : 0 ≤ N) (ζ : ℝ) : Real.sqrt (N ^ (2 * ζ)) = N ^ ζ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN]; congr 1; ring

/-- The Hermitian matrix of the carrier. -/
private theorem GreenLocal_hermitian {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA (BAflowLam0 sz z) n t ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n t ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (BAflowLam0 sz z n : ℂ) = (BAflowLam0 sz z n : ℂ) from Complex.conj_ofReal _]

/-- `‖𝓛^{(2)}_{(-,+),(a,b)}‖ = W^{-2d} Σ_{x∈a, y∈b} |G_{xy}|²` along the flow (`GreenOff_loop_eq`). -/
private theorem GreenLocal_loop_link {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    ‖(baFMz sz z).L n t ![false, true] ![a, b] ω‖ = GreenCore_loop (GreenCore_Gc sz z n t ω) a b :=
  GreenOff_loop_eq (GreenLocal_hermitian sz z n t ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) a b

private theorem GreenLocal_loop_le_max {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    GreenCore_loop (GreenCore_Gc sz z n t ω) a b ≤ STmaxLoop2g (baFMz sz z) n t ω := by
  rw [← GreenLocal_loop_link]
  exact Finset.le_sup' (f := fun p : Zd d (sz.L n) × Zd d (sz.L n) => ‖(baFMz sz z).L n t ![false, true] ![p.1, p.2] ω‖)
    (Finset.mem_univ (a, b))

private theorem GreenLocal_max_nonneg {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    0 ≤ STmaxLoop2g (baFMz sz z) n t ω :=
  (norm_nonneg _).trans (Finset.le_sup' (f := fun p : Zd d (sz.L n) × Zd d (sz.L n) =>
    ‖(baFMz sz z).L n t ![false, true] ![p.1, p.2] ω‖) (Finset.mem_univ ((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n)))))

/-- `N^{ζ} W^{-ε₀} ≤ W^{-ε₀/2}` eventually, for `ζ = 𝔠 ε₀/2` (`W ≥ N^𝔠`). -/
private theorem GreenLocal_ev_incl {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by
  filter_upwards [hA.2.2.2.1] with n hn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 2) := by
    calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (ε₀ / 2) := by
          rw [← Real.rpow_mul hN0]; congr 1; ring
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 2) := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hn (by linarith)
  calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀)
      ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₀ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ / 2)) := by rw [← Real.rpow_add hW0]; congr 1; ring

/-- `C N^σ ≤ N^τ` eventually, for `σ < τ`. -/
private theorem GreenLocal_ev_pow {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) (C : ℝ) {σ τ : ℝ} (hστ : σ < τ) :
    ∀ᶠ n in atTop, C * ((sz.size n : ℕ) : ℝ) ^ σ ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
  have hlim := (tendsto_rpow_atTop (show 0 < τ - σ by linarith)).comp hsz
  filter_upwards [hlim.eventually_ge_atTop C, hsz.eventually_ge_atTop 1] with n h1 h2
  have h3 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ σ := Real.rpow_nonneg (by linarith) _
  calc C * ((sz.size n : ℕ) : ℝ) ^ σ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - σ) * ((sz.size n : ℕ) : ℝ) ^ σ :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = ((sz.size n : ℕ) : ℝ) ^ τ := by rw [← Real.rpow_add (by linarith)]; congr 1; ring

end Helpers

/-! ## 3. GL5: the event `{‖G_t - M‖_max ≤ N^ζ W^{-ε₀}}` -/

/-- **GL5**: from (A) of `(initialGT2)` the event `Ω_ζ = {‖G_t - M‖_max ≤ N^ζ W^{-ε₀}}` has high probability, and
`N^ζ W^{-ε₀} ≤ κ/2` eventually, for `0 < ζ ≤ 𝔠 ε₀/2` (`W ≥ N^𝔠`).  No guard on `d`; the bridge `δ_n = N^ζ W^{-ε₀}` of G5c
(`BAIBPDet`). -/
theorem greenLocal_omega (d : ℕ) : GreenLocal_omega d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ hA ζ hζ hζ𝔠
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  refine ⟨?_, ?_⟩
  · filter_upwards [GreenOff_ev_small sz hflow.1 hε₀ (τ₀ := 2 * ζ) (by linarith) (half_pos hκ)] with n hn
    rwa [GreenLocal_sqrt_rpow (Nat.cast_nonneg _)] at hn
  · exact (StochDomAt.highProb hA hζ).mono (Eventually.of_forall fun n ω hω x y => hω (x, y))

/-! ## 4. GL2: the diagonal law `BAGbEXPii`

The constant of the diagonal law: `8 K_BA² (9/4 A_b + X_b) ≤ C_gii Φ² 𝓛_max` under `Φ ≥ 1`, `δ ≤ κ/2`, `g₀ ≤ Λ` and the floor
`W^{-d} ≤ (4/κ²) 𝓛_max` (GL1).  `C_gii` is a function of `(d, κ, c₀, ρ, S, Λ)`, hence of `(d, κ, 𝔡)` only. -/

section Constants

/-- `R₀ ≤ Φ q 𝓛_max`, `q = 16 c₀⁻² S κ⁻² + 16 ρ c₀⁻¹ S²`. -/
private def GreenLocal_q (κ c₀ ρ S : ℝ) : ℝ := 16 * c₀⁻¹ ^ 2 * S * κ⁻¹ ^ 2 + 16 * ρ * c₀⁻¹ * S ^ 2

private def GreenLocal_Cgl (d : ℕ) (κ c₀ ρ S Λ : ℝ) : ℝ :=
  9 / 4 * (5 * (13 / 4 * GreenLocal_q κ c₀ ρ S + 2 + 13 / 2 * GreenLocal_q κ c₀ ρ S + 4 / κ ^ 2 +
    (2 * d * Λ) ^ 2 * ((2 + 18 / κ ^ 2) * GreenLocal_q κ c₀ ρ S))) + (2 + 18 / κ ^ 2) * GreenLocal_q κ c₀ ρ S

private theorem GreenLocal_q_nonneg {κ c₀ ρ S : ℝ} (hc₀ : 0 < c₀) (hρ : 0 ≤ ρ) (hS : 0 ≤ S) : 0 ≤ GreenLocal_q κ c₀ ρ S := by
  unfold GreenLocal_q; positivity

private theorem GreenLocal_R0_le {κ c₀ ρ S Φ w₀ Lm : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) (hρ : 0 ≤ ρ) (hS : 0 ≤ S)
    (hΦ : 1 ≤ Φ) (hLm0 : 0 ≤ Lm) (hw : w₀ ≤ 4 / κ ^ 2 * Lm) :
    GreenCore_R0 c₀ ρ S Φ w₀ Lm ≤ Φ * GreenLocal_q κ c₀ ρ S * Lm := by
  have h1 : 4 * c₀⁻¹ ^ 2 * S * w₀ ≤ 16 * c₀⁻¹ ^ 2 * S * κ⁻¹ ^ 2 * Lm := by
    calc 4 * c₀⁻¹ ^ 2 * S * w₀ ≤ 4 * c₀⁻¹ ^ 2 * S * (4 / κ ^ 2 * Lm) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = 16 * c₀⁻¹ ^ 2 * S * κ⁻¹ ^ 2 * Lm := by rw [div_eq_mul_inv, inv_pow]; ring
  have h2 : 16 * c₀⁻¹ ^ 2 * S * κ⁻¹ ^ 2 * Lm ≤ Φ * (16 * c₀⁻¹ ^ 2 * S * κ⁻¹ ^ 2) * Lm := by
    have h0 : 0 ≤ 16 * c₀⁻¹ ^ 2 * S * κ⁻¹ ^ 2 := by positivity
    nlinarith [mul_nonneg h0 hLm0]
  unfold GreenCore_R0 GreenLocal_q
  nlinarith

/-- **The constant of the diagonal law.** -/
private theorem GreenLocal_diag_bound {d : ℕ} {κ c₀ ρ S g₀ Λ Φ δ w₀ Lm : ℝ} (hκ : 0 < κ) (hc₀ : 0 < c₀) (hρ : 0 ≤ ρ)
    (hS : 0 ≤ S) (hg0 : 0 ≤ g₀) (hgΛ : g₀ ≤ Λ) (hΦ : 1 ≤ Φ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ κ / 2) (hLm0 : 0 ≤ Lm) (hw0 : 0 ≤ w₀)
    (hw : w₀ ≤ 4 / κ ^ 2 * Lm) :
    9 / 4 * GreenCore_Ab d κ Φ δ c₀ ρ S g₀ w₀ Lm + GreenCore_Xb κ Φ c₀ ρ S w₀ Lm ≤
      GreenLocal_Cgl d κ c₀ ρ S Λ * (Φ ^ 2 * Lm) := by
  have hq := GreenLocal_q_nonneg (κ := κ) hc₀ hρ hS
  have hR0 := GreenLocal_R0_le hκ hc₀ hρ hS hΦ hLm0 hw
  have hΦ0 : 0 ≤ Φ := by linarith
  have hκ2 : 0 < κ ^ 2 := by positivity
  set q := GreenLocal_q κ c₀ ρ S with hqdef
  set R0 := GreenCore_R0 c₀ ρ S Φ w₀ Lm with hR0def
  have hR0nn : 0 ≤ R0 := by
    rw [hR0def]; unfold GreenCore_R0
    have : 0 ≤ 4 * c₀⁻¹ ^ 2 * S * w₀ + 16 * ρ * Φ * c₀⁻¹ * S * (S * Lm) := by positivity
    exact this
  set T := Φ ^ 2 * Lm with hT
  have hT0 : 0 ≤ T := by positivity
  have hΦΦ : Φ ≤ Φ ^ 2 := by nlinarith
  -- `X_b ≤ (2 + 18/κ²) q T`
  have hXb : GreenCore_Xb κ Φ c₀ ρ S w₀ Lm ≤ (2 + 18 / κ ^ 2) * q * T := by
    unfold GreenCore_Xb
    rw [← hR0def]
    have h18 : 0 ≤ 2 + 18 / κ ^ 2 := by positivity
    calc Φ * (2 + 18 / κ ^ 2) * R0 ≤ Φ * (2 + 18 / κ ^ 2) * (Φ * q * Lm) :=
          mul_le_mul_of_nonneg_left hR0 (by positivity)
      _ = (2 + 18 / κ ^ 2) * q * T := by rw [hT]; ring
  -- the pieces of `A_b`
  have hd2 : δ ^ 2 ≤ κ ^ 2 / 4 := by nlinarith
  have hk1 : 4 / κ ^ 2 * (13 / 4 * δ ^ 2) ≤ 13 / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hκ2]; nlinarith
  have hk2 : 8 / κ ^ 2 * (13 / 4 * δ ^ 2) ≤ 13 / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hκ2]; nlinarith
  have p1 : 4 / κ ^ 2 * R0 * (13 / 4 * δ ^ 2) ≤ 13 / 4 * q * T := by
    calc 4 / κ ^ 2 * R0 * (13 / 4 * δ ^ 2) = R0 * (4 / κ ^ 2 * (13 / 4 * δ ^ 2)) := by ring
      _ ≤ R0 * (13 / 4) := mul_le_mul_of_nonneg_left hk1 hR0nn
      _ ≤ (Φ * q * Lm) * (13 / 4) := mul_le_mul_of_nonneg_right hR0 (by norm_num)
      _ ≤ 13 / 4 * q * T := by rw [hT]; nlinarith [mul_nonneg hq hLm0, mul_nonneg (mul_nonneg hq hLm0) (sub_nonneg.2 hΦΦ)]
  have p2 : Φ * (2 * Lm + 8 / κ ^ 2 * R0 * (13 / 4 * δ ^ 2)) ≤ (2 + 13 / 2 * q) * T := by
    have e1 : 8 / κ ^ 2 * R0 * (13 / 4 * δ ^ 2) ≤ 13 / 2 * R0 := by
      calc 8 / κ ^ 2 * R0 * (13 / 4 * δ ^ 2) = R0 * (8 / κ ^ 2 * (13 / 4 * δ ^ 2)) := by ring
        _ ≤ R0 * (13 / 2) := mul_le_mul_of_nonneg_left hk2 hR0nn
        _ = 13 / 2 * R0 := by ring
    calc Φ * (2 * Lm + 8 / κ ^ 2 * R0 * (13 / 4 * δ ^ 2)) ≤ Φ * (2 * Lm + 13 / 2 * R0) :=
          mul_le_mul_of_nonneg_left (by linarith) hΦ0
      _ ≤ Φ * (2 * Lm + 13 / 2 * (Φ * q * Lm)) := mul_le_mul_of_nonneg_left (by linarith) hΦ0
      _ = 2 * (Φ * Lm) + 13 / 2 * q * (Φ ^ 2 * Lm) := by ring
      _ ≤ (2 + 13 / 2 * q) * T := by
          rw [hT]; nlinarith [mul_nonneg hLm0 (sub_nonneg.2 hΦΦ)]
  have p3 : Φ * w₀ ≤ 4 / κ ^ 2 * T := by
    calc Φ * w₀ ≤ Φ * (4 / κ ^ 2 * Lm) := mul_le_mul_of_nonneg_left hw hΦ0
      _ = 4 / κ ^ 2 * (Φ * Lm) := by ring
      _ ≤ 4 / κ ^ 2 * T := by
          rw [hT]; exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hLm0 (sub_nonneg.2 hΦΦ)]) (by positivity)
  have p4 : (2 * d * g₀) ^ 2 * GreenCore_Xb κ Φ c₀ ρ S w₀ Lm ≤ (2 * d * Λ) ^ 2 * ((2 + 18 / κ ^ 2) * q * T) := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hXb0 : 0 ≤ GreenCore_Xb κ Φ c₀ ρ S w₀ Lm := by
      unfold GreenCore_Xb; positivity
    calc (2 * d * g₀) ^ 2 * GreenCore_Xb κ Φ c₀ ρ S w₀ Lm ≤ (2 * d * Λ) ^ 2 * GreenCore_Xb κ Φ c₀ ρ S w₀ Lm :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by nlinarith) 2) hXb0
      _ ≤ _ := mul_le_mul_of_nonneg_left hXb (by positivity)
  have hAb : GreenCore_Ab d κ Φ δ c₀ ρ S g₀ w₀ Lm ≤
      5 * (13 / 4 * q * T + (2 + 13 / 2 * q) * T + 4 / κ ^ 2 * T + (2 * d * Λ) ^ 2 * ((2 + 18 / κ ^ 2) * q * T)) := by
    unfold GreenCore_Ab
    rw [← hR0def]
    exact mul_le_mul_of_nonneg_left (by linarith [p1, p2, p3, p4]) (by norm_num)
  unfold GreenLocal_Cgl
  rw [← hqdef]
  linarith [hAb, hXb]

end Constants

section GiiSample

variable {d : ℕ}

/-- `K_BA = ρ (1 + ρ₂ K_Θ)` with `ρ₂ = 1`, `K_Θ = 16 κ⁻⁴` (`baM_rho2`, `baStab_holds`). -/
private def GreenLocal_KBA (d : ℕ) (κ 𝔡 : ℝ) : ℝ := GreenOff_rho d 𝔡⁻¹ κ * (1 + 1 * (16 * κ⁻¹ ^ 4))

/-- `C₂ = 8 K_BA² C_gii`. -/
private def GreenLocal_C2 (d : ℕ) (κ 𝔡 : ℝ) : ℝ :=
  8 * GreenLocal_KBA d κ 𝔡 ^ 2 * GreenLocal_Cgl d κ (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ) 𝔡⁻¹

/-- **The diagonal law, one sample**: on `Ω = {‖G_t - M‖_max ≤ δ}`, `δ ≤ κ/2`, the four large deviation events at the factor
`P ≥ 1`, (C1) and `K_BA δ ≤ 1/2`: `|(G_t - M)_{xy}|² ≤ C₂ P² 𝓛_max` (`GreenCore_diag` with the floor GL1). -/
private theorem GreenLocal_gii_sample (hd : 2 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ)
    {P δ : ℝ} (hg : 0 < BAflowLam0 sz z n) (hgΛ : BAflowLam0 sz z n ≤ 𝔡⁻¹)
    (hP : 1 ≤ P) (hδ : δ ≤ κ / 2) (hδ0 : 0 ≤ δ) (hwd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ δ ^ 2)
    (hΩ : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n t ω x y‖ ≤ δ)
    (hLrow : LDERow (GreenCore_Xc sz n t ω) (GreenCore_Gc sz z n t ω) (svar d (sz.L n) (sz.W n) 0) P)
    (hLcol : LDECol (GreenCore_Xc sz n t ω) (GreenCore_Gc sz z n t ω) (svar d (sz.L n) (sz.W n) 0) P)
    (hLquad : LDEQuad (GreenCore_Xc sz n t ω) (GreenCore_Gc sz z n t ω) (svar d (sz.L n) (sz.W n) 0) t P)
    (hLdiag : ∀ i, ‖GreenCore_Xc sz n t ω i i‖ ^ 2 ≤ P * svar d (sz.L n) (sz.W n) 0 i i)
    (hC1 : 8 * GreenOff_rho d 𝔡⁻¹ κ * ((BAct_rate d 𝔡⁻¹ κ)⁻¹ * GreenOff_S d 𝔡⁻¹ κ) *
      GreenCore_theta d κ P δ (BAflowLam0 sz z n) ≤ 1)
    (hKδ : GreenLocal_KBA d κ 𝔡 * δ ≤ 1 / 2) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).GM n t ω x y‖ ^ 2 ≤ GreenLocal_C2 d κ 𝔡 * (P ^ 2 * STmaxLoop2g (baFMz sz z) n t ω) := by
  have hd0 : 0 < d := by omega
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 hflow.1.2.1
  obtain ⟨ht1, hr, hmi, hzi, -, -⟩ := ba_G_data hκ sz hflow n ht0 htT
  obtain ⟨hGR, hRG, hMR, hMR', hz, hM, hMd, hD, hG0⟩ := GreenCore_carrier hκ sz hflow n ht0 htT ω
    (m := BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (s := (BAflowEs sz z n : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (zt := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) rfl rfl rfl
  have hc₀ := BAct_rate_pos d 𝔡⁻¹ κ hd0 hΛ hκ
  have hL3 := sz.three_le_L n
  have hdec : ∀ a b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b‖ ≤
      (BAct_rate d 𝔡⁻¹ κ)⁻¹ * Real.exp (-BAct_rate d 𝔡⁻¹ κ * (zdistD d (sz.L n) (a - b) : ℝ)) :=
    fun a b => BAMB_decay_large d (sz.L n) hL3 hd0 𝔡⁻¹ (BAflowLam0 sz z n) κ (BAflowEs sz z n) _ hΛ hg hgΛ hκ hr a b
  have hS : ∀ a : Zd d (sz.L n), ∑ b, Real.exp (-(BAct_rate d 𝔡⁻¹ κ / 2) * (zdistD d (sz.L n) (a - b) : ℝ)) ≤
      GreenOff_S d 𝔡⁻¹ κ := fun a => by
    have := BAsum_exp_decay_le d (sz.L n) hd (BAct_rate d 𝔡⁻¹ κ / 2) (by positivity) a
    unfold GreenOff_S
    simpa only [neg_mul] using this
  have hMb1 : ∀ a b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b‖ ≤ 1 := by
    intro a b
    have h1 := BAMB_row_sq_real d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) _ hr.1 a
    have h2 : ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b‖ ^ 2 ≤ 1 :=
      h1 ▸ Finset.single_le_sum (f := fun b => ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ b)
    nlinarith [norm_nonneg (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b)]
  have hκm : κ ≤ ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ := hr.2.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have hm1 : ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 :=
    BAm_norm_le_one d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) _ (by simp) hr.1
  have hρc : ∀ c, ∑ b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) b c‖ ≤
      GreenOff_rho d 𝔡⁻¹ κ := fun c => baM_col_l1 hd hL3 𝔡⁻¹ (BAflowLam0 sz z n) κ (BAflowEs sz z n) _ hΛ hg hgΛ hκ hr c
  have hρr : ∀ a, ∑ b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b‖ ≤
      GreenOff_rho d 𝔡⁻¹ κ := fun a => baM_row_l1 hd hL3 𝔡⁻¹ (BAflowLam0 sz z n) κ (BAflowEs sz z n) _ hΛ hg hgΛ hκ hr a
  have hρ₂ : ∀ a c, ∑ b, ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) a b‖ *
      ‖BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) b c‖ ≤ 1 :=
    fun a c => baM_rho2 _ _ _ hr.1 a c
  have hΩ' : ∀ u v : Vtx d (sz.L n) (sz.W n), ‖GreenCore_Gc sz z n t ω u v - GreenCore_Mc sz z n u v‖ ≤ δ := fun u v =>
    hΩ ((splitEquiv d (sz.L n) (sz.W n)).symm u) ((splitEquiv d (sz.L n) (sz.W n)).symm v)
  have hLm : ∀ a b, GreenCore_loop (GreenCore_Gc sz z n t ω) a b ≤ STmaxLoop2g (baFMz sz z) n t ω :=
    fun a b => GreenLocal_loop_le_max sz z n t ω a b
  have hLm0 := GreenLocal_max_nonneg sz z n t ω
  have hstab := baStab_holds d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) _ hκ hr t ht0 ht1.le
  have key := GreenCore_diag hL3 hGR hRG hMR hMR' hz hM hMd hD hκ hκm hm1 hMb1 hc₀ hdec hρc hS hg.le ht0 ht1.le hP hδ hδ0 hwd hΩ'
    hLrow hLcol hLquad hLdiag hC1 hLm hLm0 rfl hstab (by positivity) hρr hρ₂ hKδ
    (splitEquiv d (sz.L n) (sz.W n) x) (splitEquiv d (sz.L n) (sz.W n) y)
  have e : (baFMz sz z).GM n t ω x y = GreenCore_Gc sz z n t ω (splitEquiv d (sz.L n) (sz.W n) x)
      (splitEquiv d (sz.L n) (sz.W n) y) - GreenCore_Mc sz z n (splitEquiv d (sz.L n) (sz.W n) x)
      (splitEquiv d (sz.L n) (sz.W n) y) := by
    simp [FlowFM.GM, baFMz, baFM, GreenCore_Gc, GreenCore_Mc, blockMat]
  rw [e]
  refine key.trans ?_
  have hρ0 : 0 ≤ GreenOff_rho d 𝔡⁻¹ κ := le_trans (Finset.sum_nonneg fun b _ => norm_nonneg _) (hρc 0)
  have hS0 : 0 ≤ GreenOff_S d 𝔡⁻¹ κ := le_trans (Finset.sum_nonneg fun b _ => (Real.exp_pos _).le) (hS 0)
  have hfl := GreenLocal_floor_sample (G := GreenCore_Gc sz z n t ω) (M := GreenCore_Mc sz z n) hκ hM hMd hκm hδ hΩ' 0
  have hw : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 4 / κ ^ 2 * STmaxLoop2g (baFMz sz z) n t ω :=
    hfl.trans (mul_le_mul_of_nonneg_left (hLm 0 0) (by positivity))
  have hb := GreenLocal_diag_bound (d := d) (c₀ := BAct_rate d 𝔡⁻¹ κ) (Φ := P) (δ := δ) (g₀ := BAflowLam0 sz z n) (Λ := 𝔡⁻¹) hκ hc₀ hρ0
    hS0 hg.le hgΛ hP hδ0 hδ hLm0 GreenCore_w_pos.le hw
  unfold GreenLocal_C2 GreenLocal_KBA
  calc 8 * (GreenOff_rho d 𝔡⁻¹ κ * (1 + 1 * (16 * κ⁻¹ ^ 4))) ^ 2 * (9 / 4 * GreenCore_Ab d κ P δ (BAct_rate d 𝔡⁻¹ κ)
        (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ) (BAflowLam0 sz z n) (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
        (STmaxLoop2g (baFMz sz z) n t ω) + GreenCore_Xb κ P (BAct_rate d 𝔡⁻¹ κ) (GreenOff_rho d 𝔡⁻¹ κ)
        (GreenOff_S d 𝔡⁻¹ κ) (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ (STmaxLoop2g (baFMz sz z) n t ω))
      ≤ 8 * (GreenOff_rho d 𝔡⁻¹ κ * (1 + 1 * (16 * κ⁻¹ ^ 4))) ^ 2 * (GreenLocal_Cgl d κ (BAct_rate d 𝔡⁻¹ κ)
        (GreenOff_rho d 𝔡⁻¹ κ) (GreenOff_S d 𝔡⁻¹ κ) 𝔡⁻¹ * (P ^ 2 * STmaxLoop2g (baFMz sz z) n t ω)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end GiiSample

section GiiPin

variable {d : ℕ}

private theorem GreenLocal_card_vtx (sz : Sizes d) (n : ℕ) : Fintype.card (Vtx d (sz.L n) (sz.W n)) = sz.size n := by
  rw [Fintype.card_congr (splitEquiv d (sz.L n) (sz.W n)).symm, sz.card_Idx]

private theorem GreenLocal_card_off (sz : Sizes d) (n : ℕ) : Fintype.card (Green.OffPair d (sz.L n) (sz.W n)) ≤ sz.size n ^ 2 := by
  calc Fintype.card (Green.OffPair d (sz.L n) (sz.W n))
      ≤ Fintype.card (Vtx d (sz.L n) (sz.W n) × Vtx d (sz.L n) (sz.W n)) := Fintype.card_subtype_le _
    _ = sz.size n ^ 2 := by rw [Fintype.card_prod, GreenLocal_card_vtx, sq]

/-- A per-time domination over a polynomially small parameter set gives a high probability event. -/
private theorem GreenLocal_whp {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {size : ℕ → ℕ} {V : ℕ → Type*}
    [∀ n, Fintype (V n)] {m : ℕ} (hV : ∀ n, Fintype.card (V n) ≤ size n ^ m) {ξ ζ : ∀ n, V n → Ω → ℝ}
    (h : Path.PerTimeDomAt P size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt P size (fun n => {ω | ∀ v, ξ n v ω ≤ (size n : ℝ) ^ τ * ζ n v ω}) :=
  StochDomAt.highProb (Path.stochDomAt_of_perTimeDomAt P size (C := (m : ℝ)) (Nat.cast_nonneg m)
    (Eventually.of_forall fun n => by rw [Real.rpow_natCast]; exact_mod_cast hV n) h) hτ

private theorem GreenLocal_rho_nonneg (hd : 0 < d) {κ 𝔡 : ℝ} (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) : 0 ≤ GreenOff_rho d 𝔡⁻¹ κ := by
  have hc₀ := BAct_rate_pos d 𝔡⁻¹ κ hd (inv_pos.2 h𝔡) hκ
  unfold GreenOff_rho expC
  positivity

/-- `W^{-d} ≤ (W^{-ε'})²` for `2 ε' ≤ d`, `W ≥ 1`. -/
private theorem GreenLocal_wd_le {W ε' : ℝ} (hW : 1 ≤ W) (hε' : ε' ≤ (d : ℝ) / 2) : (W ^ d)⁻¹ ≤ (W ^ (-ε')) ^ 2 := by
  have hW0 : 0 < W := by linarith
  rw [← Real.rpow_natCast, ← Real.rpow_neg hW0.le, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  exact Real.rpow_le_rpow_of_exponent_le hW (by push_cast; linarith)

/-- **GL2 `baGbEXPii_holds`**: the pin `BAGbEXPii` (`lem_GbEXP_BA`, `(GiiGEX)`, event form, `7_8:1916-1946`) for `2 ≤ d` (the guard of
`baGbEXPij'_holds`, `BA/GreenOff.lean:1289`; paper-delta `T2408b`).  Proof: with `ε' = min(ε₀, d/2)`, `τ₀ = min(τ/4, 𝔠 ε')` and
`Φ = N^{τ₀}` the four large deviation events (`baLDEin_holds`) hold with high probability; on them and on
`Ω(ε₀) ⊆ Ω(ε')`, for `n` large (`W ≥ N^𝔠`; `GreenOff_pin_consts`: `δ = W^{-ε'} ≤ κ/2`, (C1), `K_BA δ ≤ 1/2`), the one-sample law
`GreenLocal_gii_sample` gives `|(G_t - M)_{xy}|² ≤ C₂ N^{2τ₀} 𝓛_max ≤ N^τ 𝓛_max`, `C₂ = C₂(d, κ, 𝔡)`. -/
theorem baGbEXPii_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPii d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀
  have hd0 : 0 < d := by omega
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨ε'', Kcl, hε''0, hKcl0, hconst⟩ := GreenOff_pin_consts (d := d) hd hκ h𝔡
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hsz' : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hsz
  obtain ⟨hRow, hCol, hQuad, hDiag⟩ := baLDEin_holds d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT
  have hKBA0 : 0 ≤ GreenLocal_KBA d κ 𝔡 := by
    unfold GreenLocal_KBA
    have := GreenLocal_rho_nonneg hd0 hκ h𝔡
    positivity
  set ε' : ℝ := min ε₀ ((d : ℝ) / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε₀ (by positivity)
  have hε'₀ : ε' ≤ ε₀ := min_le_left _ _
  have hε'd : ε' ≤ (d : ℝ) / 2 := min_le_right _ _
  set ε3 : ℝ := min ε'' (1 / (2 * (GreenLocal_KBA d κ 𝔡 + 1))) with hε3
  have hε30 : 0 < ε3 := lt_min hε''0 (by positivity)
  intro τ hτ D' hD'
  obtain ⟨τ₀, hτ₀0, hτ₀τ, hτ₀c⟩ : ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ ≤ τ / 4 ∧ τ₀ ≤ 𝔠 * ε' :=
    ⟨min (τ / 4) (𝔠 * ε'), lt_min (by linarith) (mul_pos h𝔠 hε'0), min_le_left _ _, min_le_right _ _⟩
  have hP1 := GreenLocal_whp (m := 2) (GreenLocal_card_off sz) hRow hτ₀0
  have hP2 := GreenLocal_whp (m := 2) (GreenLocal_card_off sz) hCol hτ₀0
  have hP3 := GreenLocal_whp (m := 1) (fun n => by rw [pow_one, GreenLocal_card_vtx sz]) hQuad hτ₀0
  have hP4 := GreenLocal_whp (m := 1) (fun n => by rw [pow_one, GreenLocal_card_vtx sz]) hDiag hτ₀0
  have hE := HighProbAt.inter hsz' hP1 (HighProbAt.inter hsz' hP2 (HighProbAt.inter hsz' hP3 hP4))
  filter_upwards [hE D' hD', BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, GreenOff_ev_small sz hflow.1 hε'0 hτ₀c hε30,
    GreenLocal_ev_pow sz hsz (GreenLocal_C2 d κ 𝔡) (σ := 2 * τ₀) (τ := τ) (by linarith)] with n hEn hg hsm hbig
  refine le_trans (MeasureTheory.measure_mono ?_) hEn
  rintro ω ⟨p, hp⟩ hωE
  obtain ⟨h1, h2, h3, h4⟩ := hωE
  obtain ⟨x, y⟩ := p
  beta_reduce at hp
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hNτ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg hN0 _
  have hLm0 := GreenLocal_max_nonneg sz z n (t n) ω
  by_cases hOm : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)
  · have hi : (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω = 1 := by simp [FlowFM.indMax, hOm]
    rw [hi, one_mul] at hp
    have hP1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀0.le
    have hδ0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε') := Real.rpow_nonneg hW0.le _
    have hΩ' : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε') := fun x y =>
      (hOm x y).trans (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith))
    have hs1 : (1 : ℝ) ≤ Real.sqrt (((sz.size n : ℕ) : ℝ) ^ τ₀) := Real.one_le_sqrt.2 hP1'
    have hδs : ((sz.W n : ℕ) : ℝ) ^ (-ε') ≤ Real.sqrt (((sz.size n : ℕ) : ℝ) ^ τ₀) * ((sz.W n : ℕ) : ℝ) ^ (-ε') :=
      le_mul_of_one_le_left hδ0 hs1
    obtain ⟨hδκ, hC1, -, -⟩ := hconst _ _ _ hP1' hδ0 hg.1.le hg.2 (hsm.trans (min_le_left _ _))
    have hKδ : GreenLocal_KBA d κ 𝔡 * ((sz.W n : ℕ) : ℝ) ^ (-ε') ≤ 1 / 2 := by
      have h5 : ((sz.W n : ℕ) : ℝ) ^ (-ε') ≤ 1 / (2 * (GreenLocal_KBA d κ 𝔡 + 1)) :=
        (hδs.trans hsm).trans (min_le_right _ _)
      calc GreenLocal_KBA d κ 𝔡 * ((sz.W n : ℕ) : ℝ) ^ (-ε') ≤ GreenLocal_KBA d κ 𝔡 * (1 / (2 * (GreenLocal_KBA d κ 𝔡 + 1))) :=
            mul_le_mul_of_nonneg_left h5 hKBA0
        _ ≤ 1 / 2 := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have key := GreenLocal_gii_sample hd hκ sz hflow n (ht0 n) (htT n) ω hg.1 hg.2 hP1' hδκ hδ0
      (GreenLocal_wd_le hW1 hε'd) hΩ' (fun i j hij => h1 ⟨(i, j), hij⟩) (fun i j hij => h2 ⟨(i, j), hij⟩) h3 h4 hC1 hKδ x y
    have hsq : (((sz.size n : ℕ) : ℝ) ^ τ₀) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (2 * τ₀) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]; congr 1; norm_num; ring
    rw [hsq] at key
    have hfin : ‖(baFMz sz z).GM n (t n) ω x y‖ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * STmaxLoop2g (baFMz sz z) n (t n) ω :=
      key.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbig hLm0)
    exact absurd hp (not_lt.2 hfin)
  · have hi : (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω = 0 := by simp [FlowFM.indMax, hOm]
    rw [hi, zero_mul] at hp
    exact absurd hp (not_lt.2 (mul_nonneg hNτ0 hLm0))

end GiiPin

end RBM.BA
