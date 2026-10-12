/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistAvgA

/-!
# BA stage TL, row TL1a (T2427), part B: Lemma T.7, Step 4, Lemma T.6, the 2p-moment recursion

Part A is `BA/TwistAvgA.lean` (the vocabulary, the pin `BATwistAvgRec`, Steps 1-3,
`twAvgMoment_holds`, `twAvgReg_holds`).  Design `docs/reports/T2413-design.md` §1, §5, §7; proofs
`docs/tickets/T2398-TL-proofs.md` T.6, T.7 (Steps 4-5, `TP:60`, `TP:80-89`).

Contents: §0 the pins of this part (`twAvgSCS`, `twAvgSPrec`, `twAvgT6`); §1 the loops of the carrier
as traces on the fine lattice and Hilbert-Schmidt sums; §2 `𝒮₁`, `𝒮₂` in offset coordinates and the
Cauchy-Schwarz step; §3 `twAvgSCS_holds` and `twAvgSPrec_holds` (`‖𝒮₁‖ + ‖𝒮₂‖ ≺ B²` from `STLmaxgL`,
`k = 2, 4`, and `BAMB_row_l1`); §4 Lemma T.6 at an arbitrary law (`twAvgT6_holds`); §5 Hölder and
Lyapunov; §6 the first display of Step 5 and `baTwistAvgRec_holds`; §7 the instances.
Private helpers carry the stem `TwistAvgA2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedFintypeInType false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.Green

/-! ## 0. The pins of part B (text of the probe `RBM3D/Probe/T2427Pins.lean` at `73b3a8d`, §§3, 4) -/

section Pins

/-- **Target 2 (ii), deterministic half** (the loop pairs of TP:83 in the mirror form): `|𝒮₁| ≤ Σ_c |M_{c₁c}| (|𝓛⁴_{(++--),(c,c₂,c,c₁)}| |𝓛²_{(+-),(c₂,c)}|)^{1/2}`,
`|𝒮₂| ≤ Σ_c |M_{c₁c}| (|𝓛⁴_{(-+-+),(c,c₂,c,c₂)}| |𝓛²_{(+-),(c,c₁)}|)^{1/2}`; pathwise. -/
def twAvgSCS (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n →
    ∀ (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)),
      ‖twAvgS1 (baFMz sz z) n t ω c₁ c₂‖ ≤ ∑ c, ‖twMB (baFMz sz z) n c₁ c‖ * Real.sqrt
        (‖(baFMz sz z).L n t ![true, true, false, false] ![c, c₂, c, c₁] ω‖ * ‖(baFMz sz z).L n t ![true, false] ![c₂, c] ω‖) ∧
      ‖twAvgS2 (baFMz sz z) n t ω c₁ c₂‖ ≤ ∑ c, ‖twMB (baFMz sz z) n c₁ c‖ * Real.sqrt
        (‖(baFMz sz z).L n t ![false, true, false, true] ![c, c₂, c, c₂] ω‖ * ‖(baFMz sz z).L n t ![true, false] ![c, c₁] ω‖)

/-- **Target 2 (ii)**: `‖𝒮₁‖ + ‖𝒮₂‖ ≺ B²` uniformly in `(c₁, c₂)`, from `STLmaxgL` (`k = 2, 4`) and `BAMB_row_l1` (the constant `C_M` is absorbed by `≺`). -/
def twAvgSPrec (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLmaxgL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n q ω => ‖twAvgS1 (baFMz sz z) n (t n) ω q.1 q.2‖ + ‖twAvgS2 (baFMz sz z) n (t n) ω q.1 q.2‖)
        (fun n _ _ => sz.Bctl n (t n) ^ 2)

/-- **Target 2 (iii)**: `𝔼[ξ Y] ≤ N^ε R 𝔼Y + N^{-D} (𝔼Y²)^{1/2}` for `ξ ≥ 0` with `ξ ≺ R` (`R ≥ 0` deterministic), `ξ ≤ N^{Kenv}` pointwise, `Y ≥ 0`
measurable with `𝔼Y² < ∞`; at an arbitrary probability law `μ` on the common sample space (the `≺` is `PrecL`, `StochDomAt` at the scale `N = sz.size n`). -/
def twAvgT6 : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] {V : ℕ → Type} (ξ : ∀ n, V n → sz.SeqΩ → ℝ) (R : ∀ n, V n → ℝ) (Kenv : ℝ),
    sz.SizeTendsto → (∀ n v ω, 0 ≤ ξ n v ω) → (∀ n v, 0 ≤ R n v) → (∀ᶠ n in atTop, ∀ v ω, ξ n v ω ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv) →
    PrecL sz μ ξ (fun n v _ => R n v) → ∀ ε D : ℝ, 0 < ε → 0 < D → ∀ᶠ n in atTop, ∀ (v : V n) (Y : sz.SeqΩ → ℝ), Measurable Y → (∀ ω, 0 ≤ Y ω) →
      Integrable (fun ω => Y ω ^ 2) μ →
      ∫ ω, ξ n v ω * Y ω ∂μ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * R n v * ∫ ω, Y ω ∂μ + ((sz.size n : ℕ) : ℝ) ^ (-D) * (∫ ω, Y ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2)

end Pins

/-! ## 1. The loops of the carrier: traces on the fine lattice, Hilbert-Schmidt sums -/

section Loops
variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `E_a` on the fine lattice: `(E_a)_{xy} = W^{-d} 1(x = y ∈ [a])`. -/
def TwistAvgA2_E (a : Zd d L) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.diagonal fun x => if (split d L W x).1 = a then (((W : ℂ) ^ d)⁻¹) else 0

theorem TwistAvgA2_Eblk (a : Zd d L) :
    Eblk d L W a = (TwistAvgA2_E d L W a).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold TwistAvgA2_E Eblk
  rw [Matrix.submatrix_diagonal_equiv]
  congr 1
  funext v
  simp only [Function.comp_apply]
  have : split d L W ((splitEquiv d L W).symm v) = v := (splitEquiv d L W).apply_symm_apply v
  rw [this]

theorem TwistAvgA2_trace_submatrix {m n : Type*} [Fintype m] [Fintype n] (e : m ≃ n) (X : Matrix n n ℂ) :
    Matrix.trace (X.submatrix e e) = Matrix.trace X := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => X i i)

/-- A loop of a fine matrix, as the trace of the product on the fine lattice. -/
theorem TwistAvgA2_loop_eq (Hf : Matrix (Idx d L W) (Idx d L W) ℂ) (zz : ℂ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    loopFine d L W Hf zz σ a = Matrix.trace (List.ofFn fun i : Fin k => Gres Hf zz (σ i) * TwistAvgA2_E d L W (a i)).prod := by
  unfold loopFine loopM
  have key : ∀ l : List (Fin k), (l.map fun i => Gres (blockMat d L W Hf) zz (σ i) * Eblk d L W (a i)).prod =
      ((l.map fun i => Gres Hf zz (σ i) * TwistAvgA2_E d L W (a i)).prod).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    intro l
    induction l with
    | nil => simp [Matrix.submatrix_one_equiv]
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rw [BAExp14a_Gres_blockMat, TwistAvgA2_Eblk, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [List.ofFn_eq_map, List.ofFn_eq_map, key, TwistAvgA2_trace_submatrix]


/-- **Hilbert-Schmidt trace**: `Tr(P E_a P^* E_b) = W^{-2d} Σ_{i∈[b]} Σ_{j∈[a]} |P_{ij}|²`. -/
theorem TwistAvgA2_HS (P : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) :
    Matrix.trace (P * TwistAvgA2_E d L W a * Pᴴ * TwistAvgA2_E d L W b) =
      ((((W : ℂ) ^ d)⁻¹) ^ 2) * ∑ i ∈ Iblk d L W b, ∑ j ∈ Iblk d L W a, ((‖P i j‖ ^ 2 : ℝ) : ℂ) := by
  have hE : ∀ c : Zd d L, TwistAvgA2_E d L W c = Matrix.diagonal (fun x : Idx d L W => if (split d L W x).1 = c then (((W : ℂ) ^ d)⁻¹) else 0) :=
    fun c => rfl
  have e1 : ∀ i : Idx d L W, (P * TwistAvgA2_E d L W a * Pᴴ * TwistAvgA2_E d L W b) i i =
      (∑ j, P i j * (if (split d L W j).1 = a then (((W : ℂ) ^ d)⁻¹) else 0) * star (P i j)) *
        (if (split d L W i).1 = b then (((W : ℂ) ^ d)⁻¹) else 0) := by
    intro i
    rw [hE a, hE b, Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  simp only [Matrix.trace, Matrix.diag, e1]
  have e2 : ∀ x : ℂ, x * star x = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; ring
  have e3 : ∀ i j : Idx d L W, P i j * (if (split d L W j).1 = a then (((W : ℂ) ^ d)⁻¹) else 0) * star (P i j) =
      (if (split d L W j).1 = a then (((W : ℂ) ^ d)⁻¹) else 0) * ((‖P i j‖ ^ 2 : ℝ) : ℂ) := fun i j => by
    rw [← e2 (P i j)]; ring
  simp only [e3]
  unfold Iblk
  simp only [Finset.sum_filter]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  by_cases hi : (split d L W i).1 = b
  · simp only [hi, ite_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (split d L W j).1 = a
    · simp [hj]; ring
    · simp [hj]
  · simp [hi]

end Loops
section CarrierLoops
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

theorem TwistAvgA2_E_conjTranspose (d L W : ℕ) [NeZero L] [NeZero W] (a : Zd d L) :
    (TwistAvgA2_E d L W a)ᴴ = TwistAvgA2_E d L W a := by
  unfold TwistAvgA2_E
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  by_cases h : (split d L W x).1 = a <;> simp [h]

theorem TwistAvgA2_L_eq {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    (baFMz sz z).L n t σ a ω = Matrix.trace (List.ofFn fun i : Fin k =>
      Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) (σ i) *
        TwistAvgA2_E d (sz.L n) (sz.W n) (a i)).prod :=
  TwistAvgA2_loop_eq d (sz.L n) (sz.W n) _ _ σ a

theorem TwistAvgA2_G_eq (x y : Idx d (sz.L n) (sz.W n)) :
    (baFMz sz z).G n t ω x y = Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true x y := rfl

theorem TwistAvgA2_Gfalse : Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) false =
    (Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true)ᴴ :=
  (lwWx_Gres_conjTranspose (BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω) _).symm

/-- `𝓛^{(2)}_{(+,-),(a,b)} = W^{-2d} Σ_{i∈[b]} Σ_{j∈[a]} |G_{ij}|²`. -/
theorem TwistAvgA2_L2 (a b : Zd d (sz.L n)) :
    (baFMz sz z).L n t ![true, false] ![a, b] ω =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ i ∈ Iblk d (sz.L n) (sz.W n) b, ∑ j ∈ Iblk d (sz.L n) (sz.W n) a,
        ((‖(baFMz sz z).G n t ω i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [TwistAvgA2_L_eq]
  have e : (List.ofFn fun i : Fin 2 => Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t)
      (![true, false] i) * TwistAvgA2_E d (sz.L n) (sz.W n) (![a, b] i)).prod =
      Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true * TwistAvgA2_E d (sz.L n) (sz.W n) a *
        (Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true)ᴴ * TwistAvgA2_E d (sz.L n) (sz.W n) b := by
    rw [← TwistAvgA2_Gfalse n t ω]
    simp [List.ofFn_succ, Matrix.mul_assoc]
  rw [e]
  exact TwistAvgA2_HS d (sz.L n) (sz.W n) _ a b


/-- `𝓛^{(4)}_{(+,+,-,-),(c,c₂,c,c₁)} = W^{-2d} Σ_{i∈[c₁]} Σ_{j∈[c₂]} |(G E_c G)_{ij}|²`. -/
theorem TwistAvgA2_L4a (c c₂ c₁ : Zd d (sz.L n)) :
    (baFMz sz z).L n t ![true, true, false, false] ![c, c₂, c, c₁] ω =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ i ∈ Iblk d (sz.L n) (sz.W n) c₁, ∑ j ∈ Iblk d (sz.L n) (sz.W n) c₂,
        ((‖(Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true *
          TwistAvgA2_E d (sz.L n) (sz.W n) c * Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true) i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [TwistAvgA2_L_eq]
  set Gm := Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true with hGm
  have e : (List.ofFn fun i : Fin 4 => Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t)
      (![true, true, false, false] i) * TwistAvgA2_E d (sz.L n) (sz.W n) (![c, c₂, c, c₁] i)).prod =
      (Gm * TwistAvgA2_E d (sz.L n) (sz.W n) c * Gm) * TwistAvgA2_E d (sz.L n) (sz.W n) c₂ *
        (Gm * TwistAvgA2_E d (sz.L n) (sz.W n) c * Gm)ᴴ * TwistAvgA2_E d (sz.L n) (sz.W n) c₁ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, TwistAvgA2_E_conjTranspose, ← TwistAvgA2_Gfalse n t ω]
    simp [List.ofFn_succ, Matrix.mul_assoc]
    rfl
  rw [e]
  exact TwistAvgA2_HS d (sz.L n) (sz.W n) _ c₂ c₁

/-- `𝓛^{(4)}_{(-,+,-,+),(c,c₂,c,c₂)} = W^{-2d} Σ_{i∈[c₂]} Σ_{j∈[c₂]} |(G^* E_c G)_{ij}|²`. -/
theorem TwistAvgA2_L4b (c c₂ : Zd d (sz.L n)) :
    (baFMz sz z).L n t ![false, true, false, true] ![c, c₂, c, c₂] ω =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ i ∈ Iblk d (sz.L n) (sz.W n) c₂, ∑ j ∈ Iblk d (sz.L n) (sz.W n) c₂,
        ((‖((Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true)ᴴ *
          TwistAvgA2_E d (sz.L n) (sz.W n) c * Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true) i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [TwistAvgA2_L_eq]
  set Gm := Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true with hGm
  have e : (List.ofFn fun i : Fin 4 => Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t)
      (![false, true, false, true] i) * TwistAvgA2_E d (sz.L n) (sz.W n) (![c, c₂, c, c₂] i)).prod =
      (Gmᴴ * TwistAvgA2_E d (sz.L n) (sz.W n) c * Gm) * TwistAvgA2_E d (sz.L n) (sz.W n) c₂ *
        (Gmᴴ * TwistAvgA2_E d (sz.L n) (sz.W n) c * Gm)ᴴ * TwistAvgA2_E d (sz.L n) (sz.W n) c₂ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, TwistAvgA2_E_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← TwistAvgA2_Gfalse n t ω]
    simp [List.ofFn_succ, Matrix.mul_assoc]
    rfl
  rw [e]
  exact TwistAvgA2_HS d (sz.L n) (sz.W n) _ c₂ c₂

end CarrierLoops
section Norms
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- `(A E_c B)_{ij} = W^{-d} Σ_o A_{i,(c,o)} B_{(c,o),j}`. -/
theorem TwistAvgA2_GEG (A B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (c : Zd d (sz.L n)) (i j : Idx d (sz.L n) (sz.W n)) :
    (A * TwistAvgA2_E d (sz.L n) (sz.W n) c * B) i j =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ o : Fin (sz.W n ^ d), A i (TwistAvgA_pt n c o) * B (TwistAvgA_pt n c o) j := by
  unfold TwistAvgA2_E
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  have h : ∀ k : Idx d (sz.L n) (sz.W n), A i k * (if (split d (sz.L n) (sz.W n) k).1 = c then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ else 0) * B k j =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (if k ∈ twBlk n c then A i k * B k j else 0) := by
    intro k
    by_cases hk : (split d (sz.L n) (sz.W n) k).1 = c
    · have : k ∈ twBlk n c := by simp [twBlk, hk]
      simp only [hk, this, ite_true]; ring
    · have : k ∉ twBlk n c := by simp [twBlk, hk]
      simp only [hk, this, ite_false]; ring
  simp only [h, ← Finset.mul_sum]
  rw [Finset.sum_ite_mem, Finset.univ_inter, TwistAvgA_sum_blk]

/-- `‖(W^{-d})² x‖ = (W^{-d})² x` for `x ≥ 0`. -/
theorem TwistAvgA2_norm_scale (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ m * (x : ℂ)‖ = ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ m * x := by
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hx]


theorem TwistAvgA2_sum_Iblk {β : Type*} [AddCommMonoid β] (c : Zd d (sz.L n)) (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, F x = ∑ o : Fin (sz.W n ^ d), F (TwistAvgA_pt n c o) :=
  TwistAvgA_sum_blk n c F

/-- `‖𝓛^{(2)}_{(+,-),(a,b)}‖ = W^{-2d} Σ_{o,o'} |G_{(b,o),(a,o')}|²`. -/
theorem TwistAvgA2_L2_norm (a b : Zd d (sz.L n)) :
    ‖(baFMz sz z).L n t ![true, false] ![a, b] ω‖ =
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d),
        ‖(baFMz sz z).G n t ω (TwistAvgA_pt n b o) (TwistAvgA_pt n a o')‖ ^ 2 := by
  rw [TwistAvgA2_L2]
  have e : ∑ i ∈ Iblk d (sz.L n) (sz.W n) b, ∑ j ∈ Iblk d (sz.L n) (sz.W n) a, ((‖(baFMz sz z).G n t ω i j‖ ^ 2 : ℝ) : ℂ) =
      ((∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖(baFMz sz z).G n t ω (TwistAvgA_pt n b o) (TwistAvgA_pt n a o')‖ ^ 2 : ℝ) : ℂ) := by
    simp only [TwistAvgA2_sum_Iblk, Complex.ofReal_sum]
  rw [e]
  exact TwistAvgA2_norm_scale n 2 _ (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)

/-- `‖𝓛^{(4)}_{(+,+,-,-),(c,c₂,c,c₁)}‖ = W^{-4d} Σ_{o,o'} |Σ_{o''} G_{(c₁,o),(c,o'')} G_{(c,o''),(c₂,o')}|²`. -/
theorem TwistAvgA2_L4a_norm (c c₂ c₁ : Zd d (sz.L n)) :
    ‖(baFMz sz z).L n t ![true, true, false, false] ![c, c₂, c, c₁] ω‖ =
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 4 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d),
        ‖∑ o'' : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o'') *
          (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o')‖ ^ 2 := by
  rw [TwistAvgA2_L4a]
  have hw : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
  have e : ∑ i ∈ Iblk d (sz.L n) (sz.W n) c₁, ∑ j ∈ Iblk d (sz.L n) (sz.W n) c₂,
      ((‖(Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true *
          TwistAvgA2_E d (sz.L n) (sz.W n) c * Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true) i j‖ ^ 2 : ℝ) : ℂ) =
      ((((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d),
        ‖∑ o'' : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o'') *
          (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o')‖ ^ 2 : ℝ) : ℂ) := by
    simp only [TwistAvgA2_sum_Iblk, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    rw [TwistAvgA2_GEG, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    simp only [TwistAvgA2_G_eq]
    push_cast
    ring
  rw [e, TwistAvgA2_norm_scale n 2 _ (by positivity)]
  ring


/-- `‖𝓛^{(4)}_{(-,+,-,+),(c,c₂,c,c₂)}‖ = W^{-4d} Σ_{o,o'} |Σ_{o''} conj G_{(c,o''),(c₂,o)} G_{(c,o''),(c₂,o')}|²`. -/
theorem TwistAvgA2_L4b_norm (c c₂ : Zd d (sz.L n)) :
    ‖(baFMz sz z).L n t ![false, true, false, true] ![c, c₂, c, c₂] ω‖ =
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 4 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d),
        ‖∑ o'' : Fin (sz.W n ^ d), (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o)) *
          (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o')‖ ^ 2 := by
  rw [TwistAvgA2_L4b]
  have hw : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
  have e : ∑ i ∈ Iblk d (sz.L n) (sz.W n) c₂, ∑ j ∈ Iblk d (sz.L n) (sz.W n) c₂,
      ((‖((Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true)ᴴ *
          TwistAvgA2_E d (sz.L n) (sz.W n) c * Gres (sz.seqHflowBA (BAflowLam0 sz z) n t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true) i j‖ ^ 2 : ℝ) : ℂ) =
      ((((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 2 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d),
        ‖∑ o'' : Fin (sz.W n ^ d), (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o)) *
          (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o')‖ ^ 2 : ℝ) : ℂ) := by
    simp only [TwistAvgA2_sum_Iblk, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    rw [TwistAvgA2_GEG, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    simp only [TwistAvgA2_G_eq, Matrix.conjTranspose_apply, Complex.star_def]
    push_cast
    ring
  rw [e, TwistAvgA2_norm_scale n 2 _ (by positivity)]
  ring

end Norms

/-! ## 2. `𝒮₁`, `𝒮₂` in offset coordinates and the Cauchy-Schwarz step (Step 4, `TP:81-83`) -/

section Expand
variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ}

theorem TwistAvgA2_cs {ι κ : Type*} [Fintype ι] [Fintype κ] (Y : ι → κ → ℂ) (Z : κ → ι → ℂ) :
    ‖∑ i, ∑ k, Y i k * Z k i‖ ≤ Real.sqrt (∑ i, ∑ k, ‖Y i k‖ ^ 2) * Real.sqrt (∑ k, ∑ i, ‖Z k i‖ ^ 2) := by
  have h1 : ‖∑ i, ∑ k, Y i k * Z k i‖ ≤ ∑ i, ∑ k, ‖Y i k‖ * ‖Z k i‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le))
  have h2 : ∑ i, ∑ k, ‖Y i k‖ * ‖Z k i‖ = ∑ p : ι × κ, ‖Y p.1 p.2‖ * ‖Z p.2 p.1‖ := by rw [Fintype.sum_prod_type]
  have h3 : (∑ p : ι × κ, ‖Y p.1 p.2‖ * ‖Z p.2 p.1‖) ^ 2 ≤ (∑ p : ι × κ, ‖Y p.1 p.2‖ ^ 2) * ∑ p : ι × κ, ‖Z p.2 p.1‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h4 : ∑ p : ι × κ, ‖Y p.1 p.2‖ ^ 2 = ∑ i, ∑ k, ‖Y i k‖ ^ 2 := Fintype.sum_prod_type _
  have h5 : ∑ p : ι × κ, ‖Z p.2 p.1‖ ^ 2 = ∑ k, ∑ i, ‖Z k i‖ ^ 2 := by rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [h2] at h1
  rw [h4, h5] at h3
  have hA : 0 ≤ ∑ i, ∑ k, ‖Y i k‖ ^ 2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rw [← Real.sqrt_mul hA]
  exact h1.trans ((le_abs_self _).trans (Real.abs_le_sqrt h3))

theorem TwistAvgA2_S_one (a b : Zd d (sz.L n)) : (baFMz sz z).S n a b = if a = b then 1 else 0 := by
  change (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b = _
  rw [Matrix.one_apply]

theorem TwistAvgA2_GPM_pt (hm : 0 < ((baFMz sz z).m n).im) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ c : Zd d (sz.L n)) (β : Idx d (sz.L n) (sz.W n))
    (o' : Fin (sz.W n ^ d)) :
    twAvgGPM (baFMz sz z) n t ω c₁ c₂ β (TwistAvgA_pt n c o') =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (twMB (baFMz sz z) n c₁ c * (baFMz sz z).G n t ω β (TwistAvgA_pt n c₂ o')) := by
  unfold twAvgGPM
  rw [TwistAvgA_sum_blk]
  simp only [TwistAvgA_shift_pt, TwistAvgA_M_pt hm, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [mul_comm]

theorem TwistAvgA2_GPG_pt (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) (α β : Idx d (sz.L n) (sz.W n)) :
    twAvgGPG (baFMz sz z) n t ω c₁ c₂ α β = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ o : Fin (sz.W n ^ d),
      (baFMz sz z).G n t ω α (TwistAvgA_pt n c₂ o) * (baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) β := by
  unfold twAvgGPG
  rw [TwistAvgA_sum_blk]
  simp only [TwistAvgA_shift_pt]


theorem TwistAvgA2_sum_ite {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq α] [AddCommMonoid γ] (c : α) (F : α → β → γ) :
    ∑ a, ∑ b, (if c = a then F a b else 0) = ∑ b, F c b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem TwistAvgA2_sum3 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid δ] (f : α → β → γ → δ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-- **`𝒮₁` in offset coordinates** (the mirror form of `TP:81`): `𝒮₁ = Σ_c M^{(B)}_{c₁c} W^{-3d} Σ_{o',o} G_{(c,o'),(c₂,o)} Σ_{o''} G_{(c₁,o),(c,o'')} G_{(c,o''),(c₂,o')}`. -/
theorem TwistAvgA2_S1_eq (hm : 0 < ((baFMz sz z).m n).im) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) :
    twAvgS1 (baFMz sz z) n t ω c₁ c₂ = ∑ c, twMB (baFMz sz z) n c₁ c * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 *
      ∑ o' : Fin (sz.W n ^ d), ∑ o : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c o') (TwistAvgA_pt n c₂ o) *
        ∑ o'' : Fin (sz.W n ^ d), ((baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o'') *
          (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o'))) := by
  unfold twAvgS1
  simp only [TwistAvgA_sum_idx, TwistAvgA2_S_one, TwistAvgA_split_pt]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, TwistAvgA2_sum_ite]
  simp only [TwistAvgA2_GPM_pt hm, TwistAvgA2_GPG_pt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o'' _ => by ring


/-- **`𝒮₂` in offset coordinates**: `𝒮₂ = Σ_c M^{(B)}_{c₁c} W^{-3d} Σ_{o,o'} conj G_{(c₁,o),(c,o')} Σ_{o''} G_{(c,o''),(c₂,o')} conj G_{(c,o''),(c₂,o)}`. -/
theorem TwistAvgA2_S2_eq (hm : 0 < ((baFMz sz z).m n).im) (t : ℝ) (ω : sz.SeqΩ) (c₁ c₂ : Zd d (sz.L n)) :
    twAvgS2 (baFMz sz z) n t ω c₁ c₂ = ∑ c, twMB (baFMz sz z) n c₁ c * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 *
      ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o')) *
        ∑ o'' : Fin (sz.W n ^ d), ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o') *
          (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o)))) := by
  unfold twAvgS2
  simp only [TwistAvgA_sum_idx, TwistAvgA2_S_one, TwistAvgA_split_pt]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, TwistAvgA2_sum_ite]
  simp only [TwistAvgA2_GPM_pt hm, TwistAvgA2_GPG_pt, map_mul, map_sum, map_inv₀, map_pow, Complex.conj_natCast, Finset.mul_sum]
  rw [TwistAvgA2_sum3]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => Finset.sum_congr rfl fun o'' _ => by ring


theorem TwistAvgA2_sqrt_arith (u A B : ℝ) (hu : 0 ≤ u) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    u ^ 3 * (Real.sqrt A * Real.sqrt B) = Real.sqrt ((u ^ 4 * B) * (u ^ 2 * A)) := by
  rw [show (u ^ 4 * B) * (u ^ 2 * A) = (u ^ 3) ^ 2 * (A * B) by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
    Real.sqrt_mul hA]

/-- **The Cauchy-Schwarz step for `𝒮₁`** (`TP:83`, mirror form): `|W^{-3d} Σ_{o',o} Y Z| ≤ (𝓛^{(4)}_{(++--),(c,c₂,c,c₁)} 𝓛^{(2)}_{(+-),(c₂,c)})^{1/2}`. -/
theorem TwistAvgA2_key1 (t : ℝ) (ω : sz.SeqΩ) (c c₁ c₂ : Zd d (sz.L n)) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 * ∑ o' : Fin (sz.W n ^ d), ∑ o : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c o') (TwistAvgA_pt n c₂ o) *
        ∑ o'' : Fin (sz.W n ^ d), ((baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o'') *
          (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o'))‖ ≤
      Real.sqrt (‖(baFMz sz z).L n t ![true, true, false, false] ![c, c₂, c, c₁] ω‖ * ‖(baFMz sz z).L n t ![true, false] ![c₂, c] ω‖) := by
  rw [TwistAvgA2_L4a_norm, TwistAvgA2_L2_norm]
  have hu0 : (0 : ℝ) ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by have := sz.W_pos n; positivity
  have hcs := TwistAvgA2_cs (fun o' o : Fin (sz.W n ^ d) => (baFMz sz z).G n t ω (TwistAvgA_pt n c o') (TwistAvgA_pt n c₂ o))
    (fun o o' : Fin (sz.W n ^ d) => ∑ o'' : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o'') *
      (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o'))
  have hA : 0 ≤ ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖(baFMz sz z).G n t ω (TwistAvgA_pt n c o) (TwistAvgA_pt n c₂ o')‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hB : 0 ≤ ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖∑ o'' : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o'') *
      (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o')‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast, ← TwistAvgA2_sqrt_arith _ _ _ hu0 hA hB]
  exact mul_le_mul_of_nonneg_left hcs (by positivity)

/-- **The Cauchy-Schwarz step for `𝒮₂`** (`TP:83`, mirror form): `|W^{-3d} Σ_{o,o'} Y₂ Z₂| ≤ (𝓛^{(4)}_{(-+-+),(c,c₂,c,c₂)} 𝓛^{(2)}_{(+-),(c,c₁)})^{1/2}`. -/
theorem TwistAvgA2_key2 (t : ℝ) (ω : sz.SeqΩ) (c c₁ c₂ : Zd d (sz.L n)) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ ^ 3 * ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d),
        (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o')) *
        ∑ o'' : Fin (sz.W n ^ d), ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o') *
          (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o)))‖ ≤
      Real.sqrt (‖(baFMz sz z).L n t ![false, true, false, true] ![c, c₂, c, c₂] ω‖ * ‖(baFMz sz z).L n t ![true, false] ![c, c₁] ω‖) := by
  rw [TwistAvgA2_L4b_norm, TwistAvgA2_L2_norm]
  have hu0 : (0 : ℝ) ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by have := sz.W_pos n; positivity
  have hcs := TwistAvgA2_cs (fun o o' : Fin (sz.W n ^ d) => (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o')))
    (fun o' o : Fin (sz.W n ^ d) => ∑ o'' : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o') *
      (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o)))
  have hA : 0 ≤ ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖(baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o')‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hB : 0 ≤ ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖∑ o'' : Fin (sz.W n ^ d), (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o)) *
      (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o')‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have e1 : ∑ i : Fin (sz.W n ^ d), ∑ k : Fin (sz.W n ^ d), ‖(starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c₁ i) (TwistAvgA_pt n c k))‖ ^ 2 =
      ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖(baFMz sz z).G n t ω (TwistAvgA_pt n c₁ o) (TwistAvgA_pt n c o')‖ ^ 2 := by
    simp only [Complex.norm_conj]
  have e2 : ∑ k : Fin (sz.W n ^ d), ∑ i : Fin (sz.W n ^ d), ‖∑ o'' : Fin (sz.W n ^ d), (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ k) *
        (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ i))‖ ^ 2 =
      ∑ o : Fin (sz.W n ^ d), ∑ o' : Fin (sz.W n ^ d), ‖∑ o'' : Fin (sz.W n ^ d), (starRingEnd ℂ) ((baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o)) *
        (baFMz sz z).G n t ω (TwistAvgA_pt n c o'') (TwistAvgA_pt n c₂ o')‖ ^ 2 := by
    rw [Finset.sum_comm (β := ℝ)]
    refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun o' _ => ?_
    simp only [mul_comm]
  rw [e1, e2] at hcs
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast, ← TwistAvgA2_sqrt_arith _ _ _ hu0 hA hB]
  exact mul_le_mul_of_nonneg_left hcs (by positivity)

end Expand

/-! ## 3. Step 4: `twAvgSCS_holds`, `twAvgSPrec_holds` -/

/-- **Target 2 (ii), deterministic half, is proved** (Step 4 of Lemma T.7, mirror form of `TP:83`). -/
theorem twAvgSCS_holds (d : ℕ) : twAvgSCS d := by
  intro κ ε 𝔠 𝔡 sz z hκ hflow n t ht0 ht ω c₁ c₂
  have hm : 0 < ((baFMz sz z).m n).im := (ba_G_data hκ sz hflow n ht0 ht).2.2.1
  constructor
  · rw [TwistAvgA2_S1_eq hm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (TwistAvgA2_key1 t ω c c₁ c₂) (norm_nonneg _)
  · rw [TwistAvgA2_S2_eq hm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (TwistAvgA2_key2 t ω c c₁ c₂) (norm_nonneg _)

/-- `Σ_c |M^{(B)}_{c₁c}| ≤ C_M` eventually, `C_M = c⁻¹ expC k c` with `c = BAct_rate (k+2) 𝔡⁻¹ κ` depending on `(d, κ, 𝔡)` only (`BAMB_row_l1`, `Λ = 𝔡⁻¹`). -/
theorem TwistAvgA2_row_l1 {k : ℕ} (κ ε 𝔠 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) (sz : Sizes (k + 2)) (z : ℕ → ℂ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, ∀ c₁ : Zd (k + 2) (sz.L n), ∑ c, ‖twMB (baFMz sz z) n c₁ c‖ ≤
      (BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC k (BAct_rate (k + 2) 𝔡⁻¹ κ) := by
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn c₁
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hmF : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := hr.1.1
  rw [twMB_ba z n hmF]
  exact BAMB_row_l1 k (sz.L n) (sz.three_le_L n) 𝔡⁻¹ (BAflowLam0 sz z n) κ (BAflowEs sz z n) _ (inv_pos.2 h𝔡) hn.1 hn.2 hκ hr c₁

theorem TwistAvgA2_CM_pos {k : ℕ} (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    0 < (BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC k (BAct_rate (k + 2) 𝔡⁻¹ κ) := by
  have hc := BAct_rate_pos (k + 2) 𝔡⁻¹ κ (by omega) (inv_pos.2 h𝔡) hκ
  unfold expC; positivity

/-- **Target 2 (ii) is proved**: `‖𝒮₁‖ + ‖𝒮₂‖ ≺ B²` (Step 4 of Lemma T.7): `StochDomAt.of_subset_union` for the two `≺` of `STLmaxgL` (`k = 4`: `B³`, `k = 2`: `B`),
the pathwise bound `twAvgSCS_holds` and `Σ_c |M^{(B)}_{c₁c}| ≤ C_M`; `(B³ B)^{1/2} = B²` is sharp. -/
theorem twAvgSPrec_holds (d : ℕ) : twAvgSPrec d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT μ hM
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hCM := TwistAvgA2_CM_pos (k := k) κ 𝔡 hκ h𝔡
  set CM := (BAct_rate (k + 2) 𝔡⁻¹ κ)⁻¹ * expC k (BAct_rate (k + 2) 𝔡⁻¹ κ) with hCMdef
  have hrow := TwistAvgA2_row_l1 κ ε 𝔠 𝔡 hκ h𝔡 sz z hflow
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have h4 := hM 4 (by norm_num)
  have h2 := hM 2 (by norm_num)
  unfold PrecL at h4 h2 ⊢
  refine StochDomAt.of_subset_union hsz h4 h2 ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hrow, hsz.eventually (eventually_le_rpow (2 * CM) (half_pos hτ))] with n hrown hCMn
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨hno4, hno2⟩ := hno
  have ht1 : t n < 1 := (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hB := (STBctl_pos sz n ht1).le
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hx0 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hN0 _
  obtain ⟨hS1, hS2⟩ := twAvgSCS_holds (k + 2) κ ε 𝔠 𝔡 sz z hκ hflow n (t n) (ht0 n) (htT n) ω q.1 q.2
  have hterm : ∀ (c₂ c₁ c : Zd (k + 2) (sz.L n)) (a : Fin 4 → Bool) (a' : Fin 4 → Zd (k + 2) (sz.L n)) (b : Fin 2 → Bool) (b' : Fin 2 → Zd (k + 2) (sz.L n)),
      Real.sqrt (‖(baFMz sz z).L n (t n) a a' ω‖ * ‖(baFMz sz z).L n (t n) b b' ω‖) ≤ N ^ (τ / 2) * B ^ 2 := by
    intro c₂ c₁ c a a' b b'
    have e4 := hno4 (a, a')
    have e2 := hno2 (b, b')
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc ‖(baFMz sz z).L n (t n) a a' ω‖ * ‖(baFMz sz z).L n (t n) b b' ω‖ ≤ (N ^ (τ / 2) * B ^ (4 - 1)) * (N ^ (τ / 2) * B ^ (2 - 1)) :=
          mul_le_mul e4 e2 (norm_nonneg _) (by positivity)
      _ = (N ^ (τ / 2) * B ^ 2) ^ 2 := by ring
  have hsum : ∀ (S : ℂ) (f : Zd (k + 2) (sz.L n) → ℝ), (∀ c, f c ≤ N ^ (τ / 2) * B ^ 2) →
      ‖S‖ ≤ ∑ c, ‖twMB (baFMz sz z) n q.1 c‖ * f c → ‖S‖ ≤ CM * (N ^ (τ / 2) * B ^ 2) := by
    intro S f hf hS
    refine hS.trans ?_
    calc ∑ c, ‖twMB (baFMz sz z) n q.1 c‖ * f c ≤ ∑ c, ‖twMB (baFMz sz z) n q.1 c‖ * (N ^ (τ / 2) * B ^ 2) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hf c) (norm_nonneg _)
      _ = (∑ c, ‖twMB (baFMz sz z) n q.1 c‖) * (N ^ (τ / 2) * B ^ 2) := (Finset.sum_mul _ _ _).symm
      _ ≤ CM * (N ^ (τ / 2) * B ^ 2) := mul_le_mul_of_nonneg_right (hrown q.1) (by positivity)
  have h1 := hsum _ _ (fun c => hterm q.2 q.1 c _ _ _ _) hS1
  have h2' := hsum _ _ (fun c => hterm q.2 q.1 c _ _ _ _) hS2
  have hfin : N ^ τ * B ^ 2 ≥ ‖twAvgS1 (baFMz sz z) n (t n) ω q.1 q.2‖ + ‖twAvgS2 (baFMz sz z) n (t n) ω q.1 q.2‖ := by
    calc ‖twAvgS1 (baFMz sz z) n (t n) ω q.1 q.2‖ + ‖twAvgS2 (baFMz sz z) n (t n) ω q.1 q.2‖ ≤ 2 * CM * (N ^ (τ / 2) * B ^ 2) := by linarith
      _ ≤ N ^ (τ / 2) * (N ^ (τ / 2) * B ^ 2) := mul_le_mul_of_nonneg_right hCMn (by positivity)
      _ = N ^ τ * B ^ 2 := by rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]
  exact absurd hq (not_lt.2 hfin)


/-! ## 4. Lemma T.6 at an arbitrary law (`TP:60`) -/

section T6

/-- Cauchy-Schwarz for an indicator: `𝔼[1_S Y] ≤ (𝔼 Y²)^{1/2} P(S)^{1/2}`. -/
theorem TwistAvgA2_indicator_cs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    {Y : Ω → ℝ} (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY2 : Integrable (fun ω => Y ω ^ 2) μ) :
    ∫ ω, S.indicator Y ω ∂μ ≤ (∫ ω, Y ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (μ.real S) ^ ((1 : ℝ) / 2) := by
  have h2 : MemLp Y (ENNReal.ofReal 2) μ := by
    have := (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).2 hY2
    simpa using this
  have h1 : MemLp (S.indicator fun _ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    have := (memLp_const (1 : ℝ) (p := 2) (μ := μ)).indicator hS
    simpa using this
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two (Eventually.of_forall hY0 : 0 ≤ᵐ[μ] Y)
    (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω) h2 h1
  have e1 : ∫ ω, Y ω * S.indicator (fun _ => (1 : ℝ)) ω ∂μ = ∫ ω, S.indicator Y ω ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ S <;> simp [Set.indicator, hω]
  have e2 : ∫ ω, (S.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ) ∂μ = μ.real S := by
    have : ∀ ω, (S.indicator (fun _ => (1 : ℝ)) ω) ^ (2 : ℝ) = S.indicator (fun _ => (1 : ℝ)) ω := fun ω => by
      by_cases hω : ω ∈ S <;> simp [Set.indicator, hω]
    simp only [this]
    rw [integral_indicator_const _ hS]
    simp
  have e3 : ∫ ω, Y ω ^ (2 : ℝ) ∂μ = ∫ ω, Y ω ^ 2 ∂μ := by simp only [Real.rpow_two]
  rw [e1, e2, e3] at h
  simpa using h


/-- **Lemma T.6 at an arbitrary probability law is proved** (`TP:60`): `𝔼[ξ Y] ≤ N^ε R 𝔼Y + N^{-D} (𝔼Y²)^{1/2}` for `ξ ≺ R`, `ξ ≤ N^{Kenv}`, `Y ≥ 0`: split on the failure
event of `ξ ≺ R` (at `τ = ε`, failure exponent `2(D + |Kenv| + 1)`), where `ξ ≤ N^{Kenv}`, and use Cauchy-Schwarz for `𝔼[1_S Y]`. -/
theorem twAvgT6_holds : twAvgT6 := by
  intro d sz μ _ V ξ R Kenv hsz hξ0 hR0 henv hprec ε D hε hD
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hsz
  have hD₁ : 0 < 2 * (D + |Kenv| + 1) := by positivity
  filter_upwards [hprec ε hε (2 * (D + |Kenv| + 1)) hD₁, henv, hsize.eventually (eventually_ge_atTop 1)] with n hP hE hN1
  intro v Y hYm hY0 hY2
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN1' : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN1
  have hN0 : 0 < N := by linarith
  set S : Set sz.SeqΩ := {ω | N ^ ε * R n v < ξ n v ω} with hS
  have hSsub : S ⊆ badSetAt sz.size ξ (fun n v _ => R n v) ε n := fun ω hω => ⟨v, hω⟩
  have hμS : (μ S).toReal ≤ N ^ (-(2 * (D + |Kenv| + 1))) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hN0.le _) ((measure_mono hSsub).trans hP)
  set S' : Set sz.SeqΩ := toMeasurable μ S with hS'
  have hS'm : MeasurableSet S' := measurableSet_toMeasurable μ S
  have hμS' : μ.real S' = (μ S).toReal := by rw [measureReal_def, hS', measure_toMeasurable]
  have hY1 : Integrable Y μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hY2) hYm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (hY0 ω)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Y ω - 1 / 2)]
  have hpt : ∀ ω, ξ n v ω * Y ω ≤ N ^ ε * R n v * Y ω + N ^ Kenv * S'.indicator Y ω := by
    intro ω
    have hy := hY0 ω
    have hRY : 0 ≤ N ^ ε * R n v * Y ω := mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0.le _) (hR0 n v)) hy
    by_cases hω : ω ∈ S'
    · rw [Set.indicator_of_mem hω]
      have := mul_le_mul_of_nonneg_right (hE v ω) hy
      linarith
    · rw [Set.indicator_of_notMem hω]
      have hωS : ω ∉ S := fun h => hω (subset_toMeasurable μ S h)
      have : ξ n v ω ≤ N ^ ε * R n v := not_lt.1 hωS
      have := mul_le_mul_of_nonneg_right this hy
      linarith
  have hint : Integrable (fun ω => N ^ ε * R n v * Y ω + N ^ Kenv * S'.indicator Y ω) μ :=
    (hY1.const_mul _).add ((hY1.indicator hS'm).const_mul _)
  have hcs := TwistAvgA2_indicator_cs μ hS'm hYm hY0 hY2
  have hroot : (μ.real S') ^ ((1 : ℝ) / 2) ≤ N ^ (-(D + |Kenv| + 1)) := by
    rw [hμS']
    calc ((μ S).toReal) ^ ((1 : ℝ) / 2) ≤ (N ^ (-(2 * (D + |Kenv| + 1)))) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow ENNReal.toReal_nonneg hμS (by norm_num)
      _ = N ^ (-(D + |Kenv| + 1)) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; ring
  have htail : N ^ Kenv * (μ.real S') ^ ((1 : ℝ) / 2) ≤ N ^ (-D) := by
    calc N ^ Kenv * (μ.real S') ^ ((1 : ℝ) / 2) ≤ N ^ Kenv * N ^ (-(D + |Kenv| + 1)) :=
          mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hN0.le _)
      _ = N ^ (Kenv + -(D + |Kenv| + 1)) := (Real.rpow_add hN0 _ _).symm
      _ ≤ N ^ (-D) := Real.rpow_le_rpow_of_exponent_le hN1' (by linarith [le_abs_self Kenv])
  have hY2' : 0 ≤ (∫ ω, Y ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (integral_nonneg fun ω => sq_nonneg _) _
  calc ∫ ω, ξ n v ω * Y ω ∂μ ≤ ∫ ω, (N ^ ε * R n v * Y ω + N ^ Kenv * S'.indicator Y ω) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ω => mul_nonneg (hξ0 n v ω) (hY0 ω)) hint (Eventually.of_forall hpt)
    _ = N ^ ε * R n v * ∫ ω, Y ω ∂μ + N ^ Kenv * ∫ ω, S'.indicator Y ω ∂μ := by
        rw [integral_add (hY1.const_mul _) ((hY1.indicator hS'm).const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ N ^ ε * R n v * ∫ ω, Y ω ∂μ + N ^ Kenv * ((∫ ω, Y ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (μ.real S') ^ ((1 : ℝ) / 2)) := by
        gcongr
    _ = N ^ ε * R n v * ∫ ω, Y ω ∂μ + (N ^ Kenv * (μ.real S') ^ ((1 : ℝ) / 2)) * (∫ ω, Y ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by ring
    _ ≤ N ^ ε * R n v * ∫ ω, Y ω ∂μ + N ^ (-D) * (∫ ω, Y ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
        gcongr

end T6

/-! ## 5. Hölder, Lyapunov (the first display of Step 5, `TP:88`) -/

section Holder
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Hölder for bounded measurable nonnegative functions on a probability space (`integral_mul_le_Lp_mul_Lq_of_nonneg`). -/
theorem TwistAvgA2_holder {P Q : ℝ} (hPQ : P.HolderConjugate Q) {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ} (hfb : ∀ ω, f ω ≤ Cf) (hgb : ∀ ω, g ω ≤ Cg) :
    ∫ ω, f ω * g ω ∂μ ≤ (∫ ω, f ω ^ P ∂μ) ^ (1 / P) * (∫ ω, g ω ^ Q ∂μ) ^ (1 / Q) := by
  refine integral_mul_le_Lp_mul_Lq_of_nonneg hPQ (Eventually.of_forall hf0) (Eventually.of_forall hg0) ?_ ?_
  · exact MemLp.of_bound hfm.aestronglyMeasurable Cf (Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (hf0 ω)]; exact hfb ω)
  · exact MemLp.of_bound hgm.aestronglyMeasurable Cg (Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (hg0 ω)]; exact hgb ω)

theorem TwistAvgA2_root_pow (I : ℝ) (hI : 0 ≤ I) (p k : ℕ) :
    (I ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ k = I ^ ((k : ℝ) / (2 * (p : ℝ))) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  congr 1
  ring

theorem TwistAvgA2_root_pow_self (I : ℝ) (hI : 0 ≤ I) (p : ℕ) (hp : 1 ≤ p) : (I ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p) = I := by
  rw [TwistAvgA2_root_pow I hI p]
  have : ((2 * p : ℕ) : ℝ) / (2 * (p : ℝ)) = 1 := by
    have hp' : (p : ℝ) ≠ 0 := by positivity
    push_cast; field_simp
  rw [this, Real.rpow_one]

/-- **Step 5, Hölder** `𝔼[f g^{2p-1}] ≤ (𝔼 f^{2p})^{1/2p} ((𝔼 g^{2p})^{1/2p})^{2p-1}`. -/
theorem TwistAvgA2_holder_nat (p : ℕ) (hp : 1 ≤ p) {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfm : Measurable f) (hgm : Measurable g) {Cf Cg : ℝ} (hfb : ∀ ω, f ω ≤ Cf) (hgb : ∀ ω, g ω ≤ Cg) :
    ∫ ω, f ω * g ω ^ (2 * p - 1) ∂μ ≤ (∫ ω, f ω ^ (2 * p) ∂μ) ^ ((1 : ℝ) / (2 * (p : ℝ))) *
      ((∫ ω, g ω ^ (2 * p) ∂μ) ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p - 1) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hP : (0 : ℝ) < 2 * (p : ℝ) := by linarith
  have hQ : (0 : ℝ) < 2 * (p : ℝ) - 1 := by linarith
  have hnat : (((2 * p - 1 : ℕ)) : ℝ) = 2 * (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hPQ : (2 * (p : ℝ)).HolderConjugate (2 * (p : ℝ) / (2 * (p : ℝ) - 1)) := by
    refine ⟨?_, hP, by positivity⟩
    field_simp
    ring
  have h := TwistAvgA2_holder μ hPQ hf0 (fun ω => pow_nonneg (hg0 ω) (2 * p - 1)) hfm (hgm.pow_const _) hfb
    (Cg := Cg ^ (2 * p - 1)) (fun ω => pow_le_pow_left₀ (hg0 ω) (hgb ω) _)
  -- convert the exponents
  have e1 : ∫ ω, f ω ^ (2 * (p : ℝ)) ∂μ = ∫ ω, f ω ^ (2 * p) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [← Real.rpow_natCast]; push_cast; rfl
  have e2 : ∫ ω, (g ω ^ (2 * p - 1)) ^ (2 * (p : ℝ) / (2 * (p : ℝ) - 1)) ∂μ = ∫ ω, g ω ^ (2 * p) ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [← Real.rpow_natCast (g ω) (2 * p - 1), ← Real.rpow_mul (hg0 ω), hnat, mul_div_cancel₀ _ hQ.ne', ← Real.rpow_natCast]
    push_cast; rfl
  rw [e1, e2] at h
  have e3 : 1 / (2 * (p : ℝ) / (2 * (p : ℝ) - 1)) = ((2 * p - 1 : ℕ) : ℝ) / (2 * (p : ℝ)) := by
    rw [hnat]; field_simp
  rw [e3] at h
  rw [TwistAvgA2_root_pow _ (integral_nonneg fun ω => pow_nonneg (hg0 ω) _) p (2 * p - 1)]
  exact h


/-- `𝔼 g^{2p-1} ≤ ((𝔼 g^{2p})^{1/2p})^{2p-1}`. -/
theorem TwistAvgA2_lyap1 (p : ℕ) (hp : 1 ≤ p) {g : Ω → ℝ} (hg0 : ∀ ω, 0 ≤ g ω) (hgm : Measurable g) {Cg : ℝ} (hgb : ∀ ω, g ω ≤ Cg) :
    ∫ ω, g ω ^ (2 * p - 1) ∂μ ≤ ((∫ ω, g ω ^ (2 * p) ∂μ) ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p - 1) := by
  have h := TwistAvgA2_holder_nat μ p hp (f := fun _ => (1 : ℝ)) (fun _ => zero_le_one) hg0 measurable_const hgm (Cf := 1) (fun _ => le_rfl) hgb
  simpa using h

/-- `𝔼 g^{2p-2} ≤ ((𝔼 g^{2p})^{1/2p})^{2p-2}` (Lyapunov; `p = 1` is `1 ≤ 1`). -/
theorem TwistAvgA2_lyap2 (p : ℕ) (hp : 1 ≤ p) {g : Ω → ℝ} (hg0 : ∀ ω, 0 ≤ g ω) (hgm : Measurable g) {Cg : ℝ} (hgb : ∀ ω, g ω ≤ Cg) :
    ∫ ω, g ω ^ (2 * p - 2) ∂μ ≤ ((∫ ω, g ω ^ (2 * p) ∂μ) ^ ((1 : ℝ) / (2 * (p : ℝ)))) ^ (2 * p - 2) := by
  rcases Nat.lt_or_ge p 2 with h1 | h2
  · have : p = 1 := by omega
    subst this
    simp
  · have hp' : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hnat : (((2 * p - 2 : ℕ)) : ℝ) = 2 * ((p : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hPQ : ((p : ℝ) / ((p : ℝ) - 1)).HolderConjugate (p : ℝ) := by
      refine ⟨?_, by positivity, by linarith⟩
      rw [inv_one]
      field_simp
      ring
    have h := TwistAvgA2_holder μ hPQ (f := fun ω => g ω ^ (2 * p - 2)) (g := fun _ => (1 : ℝ)) (fun ω => pow_nonneg (hg0 ω) _)
      (fun _ => zero_le_one) (hgm.pow_const _) measurable_const (Cf := Cg ^ (2 * p - 2)) (fun ω => pow_le_pow_left₀ (hg0 ω) (hgb ω) _)
      (Cg := 1) (fun _ => le_rfl)
    have e2 : ∫ ω, (g ω ^ (2 * p - 2)) ^ ((p : ℝ) / ((p : ℝ) - 1)) ∂μ = ∫ ω, g ω ^ (2 * p) ∂μ := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      dsimp only
      rw [← Real.rpow_natCast (g ω) (2 * p - 2), ← Real.rpow_mul (hg0 ω), hnat, ← Real.rpow_natCast]
      congr 1
      push_cast
      field_simp
    have e3 : 1 / ((p : ℝ) / ((p : ℝ) - 1)) = ((2 * p - 2 : ℕ) : ℝ) / (2 * (p : ℝ)) := by
      rw [hnat]; field_simp
    simp only [mul_one, Real.one_rpow, integral_const, probReal_univ, smul_eq_mul] at h
    rw [e2, e3] at h
    rw [TwistAvgA2_root_pow _ (integral_nonneg fun ω => pow_nonneg (hg0 ω) _) p (2 * p - 2)]
    exact h

end Holder

end RBM.BA

end
