/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GreenSchur
import RBM3D.BA.FlowPins
import RBM3D.Green.EntryDom
import RBM3D.Green.LDE
import RBM3D.Green.IBPPoly

/-!
# The large deviation inputs of the block Anderson resolvent (BA-G2)

Ticket T2389.  Paper: `paper/tex/7_8_light_weight.tex` (`7_8:line`), `paper/tex/1_2_Intro_model_result.tex`.
The block Anderson flow is `H_t = D + X_t` with `D = g₀ Ψ` deterministic and Hermitian and `X_t` the Gaussian
part, the model of `sz.withLam 0` (`Gauss/BlockAnderson.lean:83`).  The band large deviation inputs of the
`(4.2)`, `(4.3)` layer (`Green/EntryDom.lean:874-886, 997-1021`) are proved in the files `Green/LDE`,
`Green/RowIndep`, `Green/IBPPoly` for a deterministic Hermitian shift `D` (the band is `D = 0`); here they are
instantiated at the block Anderson carrier.

* `BAGt_eq_green`: `G_t` of the carrier is `green (D + X) z_t`.
* `ba_G_data`: the data facts of the rows (`t < 1`, `Im z_t > 0`, ...), from `BAFlow` and `0 ≤ t ≤ T₀` only.
* `BAX`, **`BALDEin`**, **`baLDEin_holds`**: the four large deviation inputs `hLrow`, `hLcol`, `hLquad`, `hLdiag`
  at the carrier, in the band text, with the profile `S^{(B)}(0) = I` (`svar d L W 0`) and the law
  `Sizes.seqP (sz.withLam 0)`.
* `GreenLDE_BAX_ae_block_support`: almost surely `X` vanishes between different blocks (zero variance, `gaussianReal_zero_var`).
* An instance at `d = 3`, `sz0`, `flow_sz0`, `t ≡ 1/2`.

No smallness of `g` and of `‖M - m₀ I‖` is used: the proof reads only `D + X` Hermitian, `Im z_t > 0` and
the independent Gaussian rows of `X`.  The row coefficients are the minors of `D + X`, which read only the
off-row coordinates of `X`, so the almost sure block support of `X` is not needed for these four inputs
(`BA/GreenSchur.lean:18`: not merged).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Matrix
open RBM RBM.Gauss RBM.Gauss.Sizes

namespace RBM.BA

/-- `G_t` of the carrier is the resolvent of `D + X`, `D = g₀ Ψ` deterministic and `X` the Gaussian part of
`sz.withLam 0` (`Sizes.seqHflowBA`, `Gauss/BlockAnderson.lean:83`). -/
theorem BAGt_eq_green {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    BAGt sz lam0 E n t ω = RBM.green ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) +
      Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => seqHflow (sz.withLam 0) n t ω i j) (ztOf (BAmF sz lam0 E n) (E n) t) := by
  unfold BAGt
  simp only [RBM.green, Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]
  rfl

/-- The BA data facts used by the G rows, from `BAFlow` and `0 ≤ t ≤ T₀` only: `t < 1`, `BAReal` at `(g₀, E, m₀)`,
`Im m₀ > 0`, `η_t > 0`, the resolvent identity `G - M = -M(√t V + t m)G`, `‖M‖_max ≤ 1`. -/
theorem ba_G_data {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) :
    t < 1 ∧ BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) ∧
      0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ∧
      0 < (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im ∧
      (∀ ω, BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω - BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n =
        -(BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n * BAflowPert sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω *
          BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω)) ∧
      ∀ x y, ‖BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n x y‖ ≤ 1 := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z h n
  have hmi : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ hr.2
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)) _
  have hzi : 0 < (z n).im := lt_of_lt_of_le hN (h.2 n).2.1
  have hmz : 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im := lt_of_lt_of_le hκ (h.2 n).1
  have ht1 : t < 1 := lt_of_le_of_lt ht (BAt0_lt_one hzi hmz)
  refine ⟨ht1, hr, hmi, ?_, fun ω => (BAGt_sub_BAMfine sz _ _ n t ω ht1 hmi).1, BAMfine_norm_le_one sz _ _ n hr.1⟩
  rw [ztOf_im]
  unfold etaOf
  exact mul_pos (by linarith) hmi

/-- The Gaussian part `X = V` of the carrier (the model of `sz.withLam 0`, `Gauss/BlockAnderson.lean:83`), on the fine lattice. -/
def BAX {d : ℕ} (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => seqHflow (sz.withLam 0) n t ω i j

/-- **The G2 target: the four large deviation inputs at the BA carrier.**  The hypotheses `hLrow, hLcol, hLquad, hLdiag` of
the band `(4.2)`, `(4.3)` layer (`Green/EntryDom.lean:874-886, 997-1021`, vocabulary `Green/EntryCore.lean:514-553`, class R):
the random row `X` against the minors of the BA resolvent `G_t = (g₀ Ψ + X - z_t)⁻¹`, profile `S^{(B)}(0) = I`. -/
def BALDEin (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Green.OffPair d (sz.L n) (sz.W n))
        (fun n u ω => Green.ldeRowLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω))
          (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2)
        (fun n u ω => Green.ldeRowRHS (svar d (sz.L n) (sz.W n) 0)
          (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) ∧
      Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Green.OffPair d (sz.L n) (sz.W n))
        (fun n u ω => Green.ldeColLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω))
          (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2)
        (fun n u ω => Green.ldeColRHS (svar d (sz.L n) (sz.W n) 0)
          (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) ∧
      Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Vtx d (sz.L n) (sz.W n))
        (fun n i ω => Green.ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω))
          (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω))
          (svar d (sz.L n) (sz.W n) 0) (t n) i)
        (fun n i ω => Green.ldeQuadRHS (svar d (sz.L n) (sz.W n) 0)
          (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) i) ∧
      Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Vtx d (sz.L n) (sz.W n))
        (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω) i i‖ ^ 2)
        (fun n i _ => svar d (sz.L n) (sz.W n) 0 i i)

/-- The fourth input `hLdiag` of `BALDEin` is the merged band theorem `stochDom_normSq_Hflow_diag` at
`sz.withLam 0` (class R: `X` is the band model of `sz.withLam 0`): no new proof. -/
theorem BALDEin_diag {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) :
    Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Vtx d (sz.L n) (sz.W n))
      (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω) i i‖ ^ 2)
      (fun n i _ => svar d (sz.L n) (sz.W n) 0 i i) :=
  Green.stochDom_normSq_Hflow_diag (sz.withLam 0) h.1.2.2.1 ht0 fun n => (ba_G_data hκ sz h n (ht0 n) (ht n)).1

/-- The shift `D = g₀ Ψ` of the carrier is Hermitian (`g₀` is real, `Ψ` is Hermitian). -/
private theorem GreenLDE_shift_isHermitian {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) :
    ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n)).IsHermitian :=
  (PsiI_isHermitian d (sz.L n) (sz.W n)).smul (by simp [IsSelfAdjoint])

/-! ### Almost sure block support of `X`

The variance profile of `sz.withLam 0` is `S^{(B)}(0) = I`: `Var X_{xy} = 0` unless `x` and `y` lie in the same block
(`(bandcwV)`, `1_2:606`), so such an entry is a Gaussian of variance `0`, hence `0` almost surely
(`gaussianReal_zero_var`: `gaussianReal μ 0 = Measure.dirac μ`).  The four inputs of `BALDEin` do not use this
(their coefficients are the minors of `D + X` and the profile `svar d L W 0` carries the support); the support is
needed by the Schur split of the BA rows (`BA/GreenSchur.lean:18`). -/

/-- A coordinate of zero variance of the model of `sz.withLam 0` vanishes almost surely. -/
private theorem GreenLDE_ae_coord_zero {d : ℕ} (sz : Sizes d) (c : Sizes.SeqCoord (sz.withLam 0))
    (hc : Sizes.seqGvar (sz.withLam 0) c = 0) : ∀ᵐ ω ∂(Sizes.seqP (sz.withLam 0)), ω c = 0 := by
  have hmap : (Sizes.seqP (sz.withLam 0)).map (fun ω => ω c) =
      ProbabilityTheory.gaussianReal 0 (Sizes.seqGvar (sz.withLam 0) c) :=
    Measure.infinitePi_map_eval _ c
  rw [hc, ProbabilityTheory.gaussianReal_zero_var] at hmap
  refine (ae_map_iff (measurable_pi_apply c).aemeasurable (measurableSet_eq_fun measurable_id measurable_const)).1 ?_
  rw [hmap]
  exact (ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const)).2 rfl

/-- The profile `S^{(B)}(0) = I` has no off-block entries. -/
private theorem GreenLDE_svarF_zero_off_block (d L W : ℕ) [NeZero L] [NeZero W] (x y : Idx d L W)
    (hb : (split d L W x).1 ≠ (split d L W y).1) : svarF d L W 0 x y = 0 := by
  have h : (split d L W x).1 - (split d L W y).1 ≠ 0 := sub_ne_zero.2 hb
  simp [svarF, SBR, sbKernelR, h]

/-- An off-block coordinate pair has zero variance in the model of `sz.withLam 0`. -/
private theorem GreenLDE_gvar_off_block {d : ℕ} (sz : Sizes d) (n : ℕ) (x y : Idx d (sz.L n) (sz.W n))
    (hb : (split d (sz.L n) (sz.W n) x).1 ≠ (split d (sz.L n) (sz.W n) y).1) (b : Bool) :
    Sizes.seqGvar (sz.withLam 0) ⟨n, (x, y, b)⟩ = 0 := by
  have hxy : x ≠ y := fun h => hb (by rw [h])
  have h0 := GreenLDE_svarF_zero_off_block d (sz.L n) (sz.W n) x y hb
  apply NNReal.eq
  change (if x = y then svarF d (sz.L n) (sz.W n) 0 x y else svarF d (sz.L n) (sz.W n) 0 x y / 2) = 0
  simp [hxy, h0]

/-- An entry of `Xentry` vanishes when its (up to four) real coordinates vanish. -/
private theorem GreenLDE_Xentry_zero (d L W : ℕ) [NeZero L] [NeZero W] (ω : Ω d L W) (x y : Idx d L W)
    (h1 : ω (x, y, true) = 0) (h2 : ω (x, y, false) = 0) (h3 : ω (y, x, true) = 0) (h4 : ω (y, x, false) = 0) :
    Xentry d L W ω x y = 0 := by
  unfold Xentry
  split_ifs
  · rw [h1, h2]; simp
  · rw [h3, h4]; simp
  · rw [h1]; simp

/-- **Almost sure block support of `X`** (the Gaussian part of the carrier): almost surely, every entry between two
different blocks vanishes, at every `n` and `t`. -/
theorem GreenLDE_BAX_ae_block_support {d : ℕ} (sz : Sizes d) (n : ℕ) (t : ℝ) :
    ∀ᵐ (ω : (sz.withLam 0).SeqΩ) ∂(Sizes.seqP (sz.withLam 0)), ∀ x y : Idx d (sz.L n) (sz.W n),
      (split d (sz.L n) (sz.W n) x).1 ≠ (split d (sz.L n) (sz.W n) y).1 → BAX sz n t ω x y = 0 := by
  rw [ae_all_iff]
  intro x
  rw [ae_all_iff]
  intro y
  by_cases hb : (split d (sz.L n) (sz.W n) x).1 = (split d (sz.L n) (sz.W n) y).1
  · exact Filter.Eventually.of_forall fun ω h => absurd hb h
  have hb' : (split d (sz.L n) (sz.W n) y).1 ≠ (split d (sz.L n) (sz.W n) x).1 := fun h => hb h.symm
  have hxt := GreenLDE_ae_coord_zero sz ⟨n, (x, y, true)⟩ (GreenLDE_gvar_off_block sz n x y hb true)
  have hxf := GreenLDE_ae_coord_zero sz ⟨n, (x, y, false)⟩ (GreenLDE_gvar_off_block sz n x y hb false)
  have hyt := GreenLDE_ae_coord_zero sz ⟨n, (y, x, true)⟩ (GreenLDE_gvar_off_block sz n y x hb' true)
  have hyf := GreenLDE_ae_coord_zero sz ⟨n, (y, x, false)⟩ (GreenLDE_gvar_off_block sz n y x hb' false)
  filter_upwards [hxt, hxf, hyt, hyf] with ω h1 h2 h3 h4 _
  change (Real.sqrt t : ℂ) * Xentry d (sz.L n) (sz.W n) (Sizes.slice (sz.withLam 0) n ω) x y = 0
  rw [GreenLDE_Xentry_zero d (sz.L n) (sz.W n) (Sizes.slice (sz.withLam 0) n ω) x y h1 h2 h3 h4, mul_zero]

/-- `PerTimeDomAt` only depends on the values of the two families. -/
private theorem GreenLDE_perTime_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ}
    {U : ℕ → Type*} {ξ ζ ξ' ζ' : ∀ l, U l → Ω → ℝ} (hξ : ∀ l u ω, ξ l u ω = ξ' l u ω)
    (hζ : ∀ l u ω, ζ l u ω = ζ' l u ω) (h : Path.PerTimeDomAt P size ξ ζ) :
    Path.PerTimeDomAt P size ξ' ζ' := by
  intro τ hτ K hK
  filter_upwards [h τ hτ K hK] with n hn u
  simpa only [hξ, hζ] using hn u

/-- **`BALDEin d`, proved** (the pin of the G2 row): the four large deviation inputs at the block Anderson carrier.
Rows and columns: the generic row and column inputs `LDE_stochDom_ldeRow_shift`, `LDE_stochDom_ldeCol_shift`
(`Green/LDE.lean`) at `sz.withLam 0`, `D = g₀ Ψ`, `z = z_t`; the quadratic form: `IBPPoly_stochDom_ldeQuad_shift`
(`Green/IBPPoly.lean`); the diagonal: `BALDEin_diag`. -/
theorem baLDEin_holds (d : ℕ) : BALDEin d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z h t ht0 ht
  have hdata := fun n => ba_G_data hκ sz h n (ht0 n) (ht n)
  have hsz : (sz.withLam 0).SizeTendsto := h.1.2.2.1
  have hz : ∀ n, (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n)).im ≠ 0 :=
    fun n => (hdata n).2.2.2.1.ne'
  have ht1 : ∀ n, t n ≤ 1 := fun n => (hdata n).1.le
  have hG : ∀ n ω, BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω =
      RBM.green (((BAflowLam0 sz z n : ℂ) • PsiI d (sz.L n) (sz.W n)) + BAX sz n (t n) ω)
        (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n)) :=
    fun n ω => BAGt_eq_green sz _ _ n (t n) ω
  have hD := fun n => GreenLDE_shift_isHermitian sz (BAflowLam0 sz z) n
  refine ⟨?_, ?_, ?_, BALDEin_diag hκ sz h ht0 ht⟩
  · exact GreenLDE_perTime_congr (fun n u ω => by rw [hG n ω]; rfl) (fun n u ω => by rw [hG n ω]; rfl)
      (Green.LDE_stochDom_ldeRow_shift (sz.withLam 0) hsz
        (fun n => (BAflowLam0 sz z n : ℂ) • PsiI d (sz.L n) (sz.W n)) hD hz ht0 ht1)
  · exact GreenLDE_perTime_congr (fun n u ω => by rw [hG n ω]; rfl) (fun n u ω => by rw [hG n ω]; rfl)
      (Green.LDE_stochDom_ldeCol_shift (sz.withLam 0) hsz
        (fun n => (BAflowLam0 sz z n : ℂ) • PsiI d (sz.L n) (sz.W n)) hD hz ht0 ht1)
  · exact GreenLDE_perTime_congr (fun n u ω => by rw [hG n ω]; rfl) (fun n u ω => by rw [hG n ω]; rfl)
      (Green.IBPPoly_stochDom_ldeQuad_shift (sz.withLam 0) hsz
        (fun n => (BAflowLam0 sz z n : ℂ) • PsiI d (sz.L n) (sz.W n)) hD hz ht0 ht1)

/-! ### A nonempty instance -/

/-- **`baLDEin_holds 3` at concrete data** (`d = 3`, `sz0`: `n = 0` has `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`;
the flow `flow_sz0`: `κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`; the time `t ≡ 1/2 ≤ T₀`, `T₀ ≥ 2/3`): every
deterministic hypothesis is discharged (the shift of the carrier is `D = g₀ Ψ`, `g₀ = √T₀ λ`). -/
example := baLDEin_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
  SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num)
  (fun n => (FlowPinsInst.half_lt_t0 n).le)

/-- The instance, as a statement: the quadratic input `hLquad` of `BALDEin` at the same data. -/
example : Path.PerTimeDomAt (Sizes.seqP (SizesInst.sz0.withLam 0)) SizesInst.sz0.size
      (U := fun n => Vtx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n))
      (fun n i ω => Green.ldeQuadLHS (blockMat 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n) (BAX SizesInst.sz0 n (1 / 2) ω))
        (blockMat 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
          (BAGt SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n (1 / 2) ω))
        (svar 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n) 0) (1 / 2) i)
      (fun n i ω => Green.ldeQuadRHS (svar 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n) 0)
        (blockMat 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)
          (BAGt SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n (1 / 2) ω)) i) :=
  (baLDEin_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => (FlowPinsInst.half_lt_t0 n).le)).2.2.1

end RBM.BA
