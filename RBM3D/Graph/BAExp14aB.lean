/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14a
import RBM3D.BA.LWPinsBA
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BASizeClaim
import RBM3D.BA.Step1Trivial
import RBM3D.BA.GreenLDE

/-!
# BA-L L4a (T2418), part B: the pin S1 of `lem:LWterm_EXP` at BA and its proof

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:7-121` (`(eq:ELW_term)`, `B:11-14`), `GGGamma` `:393-405` (D402
coefficient `W - 1 = M⁺S⁺`), `lanlw` `:359-372`; design `docs/reports/T2398-design.md` §1, §2; consumer `BALWCutExpTw`
(`t/T2398:RBM3D/Probe/T2398Pins.lean:434-440`).

`BAExp14aS1` (S1, copied verbatim from the probe `t/T2418:RBM3D/Probe/T2418Pins.lean:35-112`, H219) is the crude families
`{MM, T1, T3A^{(0)}, T3A^{(1)}, F_C1, F_C2}` of `lem:LWterm_EXP` at the carrier `baFMz` and the law `seqP (sz.withLam 0)`, from the two premises
`STLocalEntrygL`, `LWAvgLawgL` only (no premise on `𝔼 tr`; Amend 1 D1).  `baExp14a_S1_holds : ∀ d, BAExp14aS1 d` is its proof.
It does **not** cover the `∂Ḡ_{xy}` children of `lanlw` on `MǦ`, `ǦM` (L4b2) nor the `∂tr` children (S3), `T2a`, `T2b`, `T3B`, `T3C`.
Not here: §6 (`lwExpI1K_holds`), §9 (`lwExpI41K_holds`), the twisted part of §8 (L4b2); no `tw*` name.

All private helpers carry the stem `BAExp14a_`.  Part A is `Graph/BAExp14a.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

section S1Fam
variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- `X_c = tr(Ǧ E_c) = W^{-d} Σ_{v ∈ [c]} Ǧ_{vv}` (`= 𝓛^{(1)}_{+,c} - m`).  With `S_{γδ} = t W^{-d} 1([γ] = [δ])` (`BAlwS`,
`Graph/BAExpand.lean:75`): `Σ_δ S_{γδ} Ǧ_{δδ} = t X_{[γ]}`. -/
def BAExp14a_X (c : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).GM n t ω v v

/-- `W^{(0)} = 1`, `W^{(1)} = W - 1`, `W = 1 + M⁺S⁺ = (1 - M⁺S)⁻¹` (`BAlwW`, `Graph/BAExpand.lean`) at the flow data of `baFMz sz z`. -/
def BAExp14a_Wk (k : Bool) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  if k then BAlwW d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) - 1 else 1

/-- The closing edge `G(σ)_{yx}`: `G_{yx}` for `σ = true`, `\overline{G_{xy}}` for `σ = false` (the entry of `G^*`). -/
def BAExp14a_tail (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then (baFMz sz z).G n t ω y x else star ((baFMz sz z).G n t ω x y)

/-- `W^{-2d} Σ_{x ∈ [a], y ∈ [b]} G(σ)_{yx} Σ_α X_{[α]} T(x, y, α)`: the frame of the families (`x ∈ [a]`, `y ∈ [b]`, `α` in the whole
fine lattice; `S^{(B)} = 1` so `a₁ = a₂ = [α]`, `B:11-14`). -/
def BAExp14a_outer (σ : Bool) (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
    BAExp14a_tail sz z n t ω σ x y * ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) * T x y α

/-- `F_MM`: `M_{xα} M_{αy}` (the two-`M` term of `G_{xα}G_{αy}`). -/
def BAExp14a_FMM (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α => (baFMz sz z).M n x α * (baFMz sz z).M n α y

/-- `F_T1`: `Σ_β (W - 1)_{αβ} M_{xβ} M_{βy}` (the first sum of `GGGamma`, D402). -/
def BAExp14a_FT1 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n x β * (baFMz sz z).M n β y

/-- `F_T3A^{(k)}`: `Σ_{w,γ} W^{(k)}_{αw} M_{wγ} · t X_{[γ]} · G_{γy} Ǧ_{xw}` (the `Ǧ_{δδ} G_{γy} Ǧ_{xw}` term of `GGGamma`, `δ`-sum done). -/
def BAExp14a_FT3A (k : Bool) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ w, ∑ γ, BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n γ)) *
      (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w

/-- `F_C1`: the `Ǧ_{ββ} G_{α'y}` child of `lanlw` on `M_{xα} Ǧ_{αy}`: `Σ_{α'} M_{xα} · t X_{[α']} M_{αα'} G_{α'y}`. -/
def BAExp14a_FC1 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ α', (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n α α' *
      (baFMz sz z).G n t ω α' y

/-- `F_C2`: the `Ǧ_{ββ} G_{α'α}` child of `lanlw` on `Ǧ_{xα} M_{αy}`: `Σ_{α'} t X_{[α']} M_{xα'} G_{α'α} M_{αy}`. -/
def BAExp14a_FC2 (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ α', ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n x α' * (baFMz sz z).G n t ω α' α *
      (baFMz sz z).M n α y

/-- The six families of S1 at the loop charge `+`, in the order `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)}, F_C1, F_C2`; `x ∈ [a]`, `y ∈ [b]`,
closing edge `G(σ)_{yx}`. -/
def BAExp14a_F (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ![BAExp14a_FMM sz z n t ω σ a b, BAExp14a_FT1 sz z n t ω σ a b, BAExp14a_FT3A sz z n t ω false σ a b,
    BAExp14a_FT3A sz z n t ω true σ a b, BAExp14a_FC1 sz z n t ω σ a b, BAExp14a_FC2 sz z n t ω σ a b] k

/-- **The integrand of S1** at the labelling of `LWcutg` (`Chain/LWGen.lean:39`): `k` the family, `σc` the charge of the loop `X` and of the two
path edges, `σo` the charge of the closing edge, `ac`, `ao` the blocks of the cut.  For `σc = true` the sum behind `LWcutg C n t true σo ac ao`
is `Σ_k F_k` over `x ∈ [ao]`, `y ∈ [ac]` (and the terms of S2, S3).  For `σc = false` the cut is the complex conjugate of the cut
`(true, !σo, ao, ac)` (cyclicity of the trace, `S = 1`: the intended reading, to be proved by the assembly), so the red families are the
conjugates of the blue ones at the swapped blocks and the same tail charge flipped. -/
def BAExp14aS1Fam (k : Fin 6) (σc σo : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  if σc then BAExp14a_F sz z n t ω k σo ao ac else star (BAExp14a_F sz z n t ω k (!σo) ac ao)

end S1Fam

/-- **S1** (the crude families of `lem:LWterm_EXP` at BA; owner T2418, row L4a): for the six families `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)},
F_C1, F_C2` (`BAExp14aS1Fam`), every charge pair `(σc, σo)` and every block pair `(ac, ao)`,
`‖𝔼 F‖ ≺ (1 - t)⁻¹ (W^{-d} B_{t,0})^{5/2}` on `U_n = {λ²/L^d ≤ 1 - t}`, over the carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`,
from the two premises `STLocalEntrygL` and `LWAvgLawgL` only (no premise on `𝔼 tr`; `STLmaxgL`, `STLKgL`, `STDecaygL`, `BATwistAvgLaw`,
`BATwistLoopLaw` of `BALWCutExpTw` are not used).  The binders, the range of `t`, `U` and the bound are those of `BALWCutExpTw`.
It does **not** cover the `∂Ḡ_{xy}` children of `lanlw` on `MǦ`, `ǦM` (L4b2) nor the `∂tr` children (S3). -/
def BAExp14aS1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : Fin 6 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, BAExp14aS1Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-! ## 1. The deterministic BA data: `M`, `Θ^{(+,+)} = ω`, `W - 1`

`M_{xy} = 1(x, y same offset) M^{(B)}_{[x][y]}` (`BAMres_fine_apply`), `ω = Θ^{(+,+)} = (1 - t M^{(B)}∘M^{(B)})⁻¹`
(`BATheta d L g E m t true true`), `(W - 1)_{αβ} = W^{-d}(ω - 1)_{[α][β]}` (design `T2398-design.md` §1.3, D402). -/

section Deterministic

private theorem BAExp14a_Msigma_shift {d L : ℕ} [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ (x + c) (y + c) = BAMsigma d L (BAMB d L g z m) σ x y := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, BAMB_shift]
  · exact BAMB_shift d L g z m x y c

/-- Translation invariance of `Θ`: `Θ(x, y) = Θ(0, y - x)` (a copy of `KInduct_theta_shift`, `BA/KInduct.lean`, private there). -/
private theorem BAExp14a_theta_shift {d L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BATheta d L g E m t s s' x y = BATheta d L g E m t s s' 0 (y - x) := by
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) s s' with hQ
  let e : Zd d L ≃ Zd d L := Equiv.addRight (-x)
  have hQe : ∀ a b, Q (e a) (e b) = Q a b := fun a b => by
    simp only [hQ, BAMss, Matrix.of_apply, e, Equiv.coe_addRight]
    rw [BAExp14a_Msigma_shift, BAExp14a_Msigma_shift]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q).submatrix e e = 1 - (t : ℂ) • Q := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQe]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • Q) e e
  rw [hA] at h2
  unfold BATheta PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  simp only [e, Equiv.coe_addRight, add_neg_cancel, ← sub_eq_add_neg] at h3
  exact h3

/-- **The `ℓ¹` rows of `ω = Θ^{(+,+)}`, uniform in `t ∈ [0,1)`** (`baProp5s_holds`; the twin of the private `KInduct_theta_l1`,
`BA/KInduct.lean:203`): `Σ_b |ω_{xb}| ≤ S`, `S = C_s (1 + Λ² expC k c_s)` depends on `(k, Λ, κ)` only. -/
theorem BAExp14a_theta_l1 {k : ℕ} (hk : 1 ≤ k) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ S : ℝ, 0 < S ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal (k + 2) L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (x : Zd (k + 2) L),
        ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖ ≤ S := by
  obtain ⟨Cs, hCs, cs, hcs, hbd⟩ := baProp5s_holds (k + 2) Λ κ (by omega) hΛ hκ
  have hexpC : 0 ≤ expC k cs := by unfold expC; positivity
  refine ⟨Cs * (1 + Λ ^ 2 * expC k cs), by positivity, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 x
  have hpt : ∀ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖
      ≤ Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
    intro b
    rw [BAExp14a_theta_shift]
    have := hbd L hL g hg hgΛ E m hr t ht0 ht1 true (b - x)
    simpa [neg_mul] using this
  have h1 : ∑ b : Zd (k + 2) L, (if b - x = 0 then (1 : ℝ) else 0) = 1 := by
    simp [sub_eq_zero]
  have h2 : ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ))) ≤ expC k cs :=
    (le_of_eq (Fintype.sum_equiv (Equiv.subRight x) _
      (fun y : Zd (k + 2) L => Real.exp (-(cs * (zdistD (k + 2) L y : ℝ)))) fun b => rfl)).trans
      (sum_radial_exp_decay_le k hcs)
  calc ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖
      ≤ ∑ b : Zd (k + 2) L, Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = Cs * (1 + g ^ 2 * ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, h1, ← Finset.mul_sum]
    _ ≤ Cs * (1 + g ^ 2 * expC k cs) := by gcongr
    _ ≤ Cs * (1 + Λ ^ 2 * expC k cs) := by
        have : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
        gcongr

/-- The columns of `ω` have the same bound (`ω` is symmetric, `BATheta_isSymm`). -/
theorem BAExp14a_theta_col {k : ℕ} {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal (k + 2) L g κ E m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) {S : ℝ}
    (hS : ∀ x : Zd (k + 2) L, ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true x b‖ ≤ S) (b : Zd (k + 2) L) :
    ∑ a : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t true true a b‖ ≤ S := by
  have hT := BATheta_isSymm (k + 2) L g κ E m hr t ht0 ht1 true true
  have : ∀ a, BATheta (k + 2) L g E m t true true a b = BATheta (k + 2) L g E m t true true b a := fun a => by
    have := congrFun (congrFun hT b) a
    simpa [Matrix.transpose_apply] using this
  simp only [this]
  exact hS b

/-- `|M_{xy}| ≤ 1` on the fine lattice (the fine Ward row `Σ_y |M_{xy}|² = 1`, `baM_row_sq`). -/
theorem BAExp14a_M_le_one {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (h : BASelf d L g0 (E : ℂ) m)
    (x y : Idx d L W) : ‖BAlwM d L W g0 E m x y‖ ≤ 1 := by
  have hrow := baM_row_sq d L W g0 E m h x
  have hle : ‖BAlwM d L W g0 E m x y‖ ^ 2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (f := fun b => ‖BAlwM d L W g0 E m x b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ y)
  nlinarith [norm_nonneg (BAlwM d L W g0 E m x y)]

/-- `M` is supported on one offset. -/
theorem BAExp14a_M_supp {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (h : BASelf d L g0 (E : ℂ) m)
    (x y : Idx d L W) (hxy : (split d L W x).2 ≠ (split d L W y).2) : BAlwM d L W g0 E m x y = 0 := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using h.1.ne'
  unfold BAlwM
  rw [BAMres_fine_apply d L W g0 (E : ℂ) m hw x y]
  simp [hxy]

/-- The fine row `ℓ¹` sum of `|M|` is the block one: `Σ_y |M_{xy}| = Σ_b |M^{(B)}_{[x] b}|`. -/
theorem BAExp14a_M_row_eq {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (h : BASelf d L g0 (E : ℂ) m)
    (x : Idx d L W) :
    ∑ y, ‖BAlwM d L W g0 E m x y‖ = ∑ b : Zd d L, ‖BAMB d L g0 (E : ℂ) m (split d L W x).1 b‖ := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using h.1.ne'
  have h1 : ∑ y, ‖BAlwM d L W g0 E m x y‖ = ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then
      ‖BAMB d L g0 (E : ℂ) m (split d L W x).1 (split d L W y).1‖ else 0) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold BAlwM
    rw [BAMres_fine_apply d L W g0 (E : ℂ) m hw x y]
    split_ifs <;> simp
  rw [h1]
  exact BASizeClaim_fibre_sum x (fun b => ‖BAMB d L g0 (E : ℂ) m (split d L W x).1 b‖)

/-- **`ℓ¹` rows of the fine `M`**, uniform in `L, W` (`BAMB_row_l1`; `d = k + 2`): `Σ_y |M_{xy}| ≤ CM = c⁻¹ expC k c`. -/
theorem BAExp14a_M_row_l1 {k : ℕ} {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ CM : ℝ, 0 < CM ∧ ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ →
      BAReal (k + 2) L g κ E m → ∀ x : Idx (k + 2) L W, ∑ y, ‖BAlwM (k + 2) L W g E m x y‖ ≤ CM := by
  have hc := BAct_rate_pos (k + 2) Λ κ (by omega) hΛ hκ
  refine ⟨(BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ), by unfold expC; positivity, ?_⟩
  intro L W _ _ hL g E m hg hgΛ hr x
  rw [BAExp14a_M_row_eq hr.1]
  exact BAMB_row_l1 k L hL Λ g κ E m hΛ hg hgΛ hκ hr _

/-- The columns: `M` is symmetric (`baM_symm`). -/
theorem BAExp14a_M_col_eq {d L W : ℕ} [NeZero L] [NeZero W] (g0 E : ℝ) (m : ℂ) (y : Idx d L W) :
    ∑ x, ‖BAlwM d L W g0 E m x y‖ = ∑ x, ‖BAlwM d L W g0 E m y x‖ :=
  Finset.sum_congr rfl fun x _ => by rw [baM_symm g0 E m x y]

/-- `lift` commutes with scalars (a copy of the private `BASizeClaim_lift_smul`). -/
private theorem BAExp14a_lift_smul {d L W : ℕ} [NeZero L] [NeZero W] (c : ℂ) (A : Matrix (Zd d L) (Zd d L) ℂ) :
    lwLift d L W (c • A) = c • lwLift d L W A := by
  ext x y; simp [lwLift]; ring

/-- `M⁺ · lift(Θ) = lift(M^{(+,+)} Θ)` (`M` is offset-diagonal: one `α` per block, `BASizeClaim_fibre_sum`). -/
theorem BAExp14a_Mp_lift {d L W : ℕ} [NeZero L] [NeZero W] {g0 E : ℝ} {m : ℂ} (hw : ((E : ℂ) + m).im ≠ 0)
    (Θ : Matrix (Zd d L) (Zd d L) ℂ) :
    BAlwMp d L W g0 E m * lwLift d L W Θ = lwLift d L W (BAMss d L (BAMB d L g0 (E : ℂ) m) true true * Θ) := by
  ext x β
  simp only [Matrix.mul_apply, lwLift, Matrix.of_apply, BAlwMp, BAlwM]
  simp only [BAMres_fine_apply d L W g0 (E : ℂ) m hw]
  have h := BASizeClaim_fibre_sum x (fun b => BAMss d L (BAMB d L g0 (E : ℂ) m) true true (split d L W x).1 b *
    Θ b (split d L W β).1)
  have h2 : ∀ α : Idx d L W,
      (if (split d L W x).2 = (split d L W α).2 then BAMB d L g0 (E : ℂ) m (split d L W x).1 (split d L W α).1 else 0) *
        (if (split d L W α).2 = (split d L W x).2 then BAMB d L g0 (E : ℂ) m (split d L W α).1 (split d L W x).1 else 0) *
        (((W : ℂ) ^ d)⁻¹ * Θ (split d L W α).1 (split d L W β).1) =
      ((W : ℂ) ^ d)⁻¹ * (if (split d L W x).2 = (split d L W α).2 then
        (fun b => BAMss d L (BAMB d L g0 (E : ℂ) m) true true (split d L W x).1 b * Θ b (split d L W β).1)
          (split d L W α).1 else 0) := by
    intro α
    by_cases ho : (split d L W x).2 = (split d L W α).2
    · have ho' : (split d L W α).2 = (split d L W x).2 := ho.symm
      rw [if_pos ho, if_pos ho', if_pos ho]
      simp only [BAMss, Matrix.of_apply, BAMsigma, ite_true]
      ring
    · have ho' : ¬ (split d L W α).2 = (split d L W x).2 := fun e => ho e.symm
      rw [if_neg ho, if_neg ho', if_neg ho]
      simp
  simp only [h2, ← Finset.mul_sum]
  rw [h]

/-- **`W - 1 = lift(ω - 1)`** (`(W - 1)_{αβ} = W^{-d} (ω - 1)_{[α][β]}`, D402, design `T2398-design.md` §1.3), `ω = Θ^{(+,+)}`: from
`W = 1 + M⁺ (S W)` (`baW_mul`) and `S W = t · lift(ω)` (`baSp_eq`). -/
theorem BAExp14a_W_sub_one {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {g0 κ E t : ℝ} {m : ℂ}
    (hr : BAReal d L g0 κ E m) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BAlwW d L W g0 E t m - 1 = lwLift d L W (BATheta d L g0 E m t true true - 1) := by
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hr.1.1.ne'
  set Q := BAMss d L (BAMB d L g0 (E : ℂ) m) true true with hQ
  set Θ := BATheta d L g0 E m t true true with hΘ
  have hU := BATheta_isUnit d L g0 κ E m hr t ht0 ht1 true true
  have h1 : (1 - (t : ℂ) • Q) * Θ = 1 := by
    have : Θ = Ring.inverse (1 - (t : ℂ) • Q) := rfl
    rw [this]
    exact Ring.mul_inverse_cancel _ hU
  have hmul := baW_mul (W := W) hL g0 E t m hr.1 ht0 ht1
  have hmul' : (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) * BAlwW d L W g0 E t m = 1 :=
    mul_eq_one_comm.1 hmul
  have hSW := baSp_eq d L W hL g0 κ E t m hr ht0 ht1
  rw [sub_mul, one_mul] at hmul'
  have hWe : BAlwW d L W g0 E t m - 1 =
      BAlwMp d L W g0 E m * (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) := by
    rw [← Matrix.mul_assoc]
    exact sub_eq_of_eq_add' (sub_eq_iff_eq_add.1 hmul')
  have hQΘ : (t : ℂ) • (Q * Θ) = Θ - 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc] at h1
    exact (sub_eq_of_eq_add' (sub_eq_iff_eq_add.1 h1)).symm
  rw [hWe, hSW, Matrix.mul_smul, BAExp14a_Mp_lift hw, ← BAExp14a_lift_smul, hQΘ]

/-- **The column sums of `W - 1`**: `Σ_α |(W - 1)_{αβ}| ≤ S + 1` from the column sums of `ω` (`≤ S`). -/
theorem BAExp14a_Wsub_col {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) {g0 κ E t : ℝ} {m : ℂ}
    (hr : BAReal d L g0 κ E m) (ht0 : 0 ≤ t) (ht1 : t < 1) {S : ℝ}
    (hS : ∀ b : Zd d L, ∑ a : Zd d L, ‖BATheta d L g0 E m t true true a b‖ ≤ S) (β : Idx d L W) :
    ∑ α : Idx d L W, ‖(BAlwW d L W g0 E t m - 1) α β‖ ≤ S + 1 := by
  rw [BAExp14a_W_sub_one hL hr ht0 ht1]
  have hWd : (0 : ℝ) < ((W : ℝ) ^ d) := by
    have : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
    positivity
  have e1 : ∀ α : Idx d L W, ‖(lwLift d L W (BATheta d L g0 E m t true true - 1)) α β‖ =
      ((W : ℝ) ^ d)⁻¹ * ‖(BATheta d L g0 E m t true true - 1) (split d L W α).1 (split d L W β).1‖ := by
    intro α
    simp only [lwLift, Matrix.of_apply, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  simp only [e1]
  rw [← Finset.mul_sum, BAExp14a_sum_blk (W := W) (fun c => ‖(BATheta d L g0 E m t true true - 1) c (split d L W β).1‖),
    ← mul_assoc, inv_mul_cancel₀ hWd.ne', one_mul]
  calc ∑ c : Zd d L, ‖(BATheta d L g0 E m t true true - 1) c (split d L W β).1‖
      ≤ ∑ c : Zd d L, (‖BATheta d L g0 E m t true true c (split d L W β).1‖ +
          (if c = (split d L W β).1 then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun c _ => ?_
        simp only [Matrix.sub_apply, Matrix.one_apply]
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
        split_ifs <;> simp
    _ = ∑ c : Zd d L, ‖BATheta d L g0 E m t true true c (split d L W β).1‖ + 1 := by
        rw [Finset.sum_add_distrib]
        simp
    _ ≤ S + 1 := by gcongr; exact hS _

end Deterministic

/-! ## 2. The scalars along the flow: `1 - t`, `η`, `B ≤ 2`, `W^{-d} ≤ (λ² + 1) B` -/

section Scalars

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- `1 - t ≥ Im z / 2` for `t ≤ t₀ = Im m/(Im m + Im z)` (`‖m‖ ≤ 1`, `Im z ≤ 1`). -/
theorem BAExp14a_one_sub_t (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ}
    (ht : t ≤ BAflowT0 sz z n) : (z n).im / 2 ≤ 1 - t := by
  obtain ⟨hzpos, hmpos, -, -⟩ := BAflow_T0_bounds hκ hflow n
  have hz1 : (z n).im ≤ 1 := (hflow.2 n).2.2
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hzpos
  have hm1 : ‖BAm d (sz.L n) (sz.lam n) (z n)‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (sz.lam n) (z n) _ hzpos.le hm
  have hmi : (BAm d (sz.L n) (sz.lam n) (z n)).im ≤ 1 := (Complex.im_le_norm _).trans hm1
  have h0 : BAflowT0 sz z n = (BAm d (sz.L n) (sz.lam n) (z n)).im /
      ((BAm d (sz.L n) (sz.lam n) (z n)).im + (z n).im) := rfl
  set mi := (BAm d (sz.L n) (sz.lam n) (z n)).im with hmi_def
  have hden : 0 < mi + (z n).im := by linarith
  have h1 : 1 - BAflowT0 sz z n = (z n).im / (mi + (z n).im) := by
    rw [h0]; field_simp; ring
  have h2 : (z n).im / 2 ≤ (z n).im / (mi + (z n).im) := by
    apply div_le_div_of_nonneg_left hzpos.le hden
    linarith
  linarith

/-- The three eventual scalar facts along the flow: `N (1 - t) ≥ 1`, `(1 - t)⁻¹ ≤ N`, `4 ≤ N`, `0 < g₀ ≤ 𝔡⁻¹`. -/
theorem BAExp14a_eventually (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧
      0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹ := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hN2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp hsz).eventually (eventually_ge_atTop 2)
  filter_upwards [hN2, hsz.eventually (eventually_ge_atTop 4), BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow]
    with n hn2 hn4 hlam
  refine ⟨?_, hn4, hlam.1, hlam.2⟩
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1 := BAExp14a_one_sub_t hκ hflow n (ht n)
  have h2 := (hflow.2 n).2.1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hpos : 0 < 1 - t n := by
    have : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) h2
    linarith
  have h3 : N * N ^ (-1 + ε) = N ^ ε := by
    rw [← Real.rpow_one_add' hN0.le (by linarith)]
    congr 1; ring
  have h4 : 1 ≤ N * (1 - t n) := by
    calc (1 : ℝ) ≤ N ^ ε / 2 := by linarith
      _ = N * N ^ (-1 + ε) / 2 := by rw [h3]
      _ ≤ N * (z n).im / 2 := by gcongr
      _ = N * ((z n).im / 2) := by ring
      _ ≤ N * (1 - t n) := by gcongr
  rw [inv_le_comm₀ hpos hN0]
  rw [inv_eq_one_div, div_le_iff₀ hN0]
  linarith

/-- `W^{-d} ≤ (λ² + 1) B` (`STBctl_ge`). -/
theorem BAExp14a_Wd_le (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n t := by
  have h := STBctl_ge sz n ht0 ht1
  have hl : 0 < sz.lam n ^ 2 + 1 := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (sz.lam n ^ 2 + 1) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹) := by
        field_simp
    _ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n t := mul_le_mul_of_nonneg_left h hl.le

end Scalars

/-! ## 3. The Ward identity of the carrier and the pathwise envelope -/

section Carrier

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- `G_t` of the carrier is the resolvent of the Hermitian `H = g₀ Ψ + H_t` at `z_t = E + (1 - t) m`. -/
theorem BAExp14a_G_green (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    (baFMz sz z).G n t ω = green (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω)
      (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) :=
  BAGt_eq_green sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω

theorem BAExp14a_eta_eq (n : ℕ) (t : ℝ) : (baFMz sz z).eta n t = etaOf ((baFMz sz z).m n) t := rfl

/-- **Fine-level Ward identities of the carrier** (row and column): `η Σ_y |G_{xy}|² = Im G_{xx}`, `η Σ_y |G_{yx}|² = Im G_{xx}`. -/
theorem BAExp14a_G_ward (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x : Idx d (sz.L n) (sz.W n)) :
    (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω x y‖ ^ 2 = ((baFMz sz z).G n t ω x x).im ∧
      (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω y x‖ ^ 2 = ((baFMz sz z).G n t ω x x).im := by
  obtain ⟨-, -, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have hz : (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t).im ≠ 0 := hzi.ne'
  have e : (baFMz sz z).eta n t = (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t).im := by
    rw [ztOf_im]; rfl
  rw [BAExp14a_G_green, e]
  exact ⟨BAExp14a_ward_row hH hz x, BAExp14a_ward_col hH hz x⟩

/-- `η > 0`. -/
theorem BAExp14a_eta_pos (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) : 0 < (baFMz sz z).eta n t := by
  obtain ⟨-, -, -, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  rw [ztOf_im] at hzi
  exact hzi

/-- `‖G_{xy}‖ ≤ η⁻¹` pathwise. -/
theorem BAExp14a_G_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).G n t ω x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ := by
  obtain ⟨-, -, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  have hH := BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω
  have hdiag : ‖(baFMz sz z).G n t ω x x‖ ≤ ((baFMz sz z).eta n t)⁻¹ := by
    have e : (baFMz sz z).eta n t = (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t).im := by
      rw [ztOf_im]; rfl
    rw [BAExp14a_G_green, e]
    exact BAExp14a_green_diag_le hH hzi x
  obtain ⟨hw, -⟩ := BAExp14a_G_ward hκ hflow n ht0 ht ω x
  have h1 : ‖(baFMz sz z).G n t ω x y‖ ^ 2 ≤ ∑ w, ‖(baFMz sz z).G n t ω x w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖(baFMz sz z).G n t ω x w‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have h2 : ((baFMz sz z).G n t ω x x).im ≤ ((baFMz sz z).eta n t)⁻¹ :=
    (Complex.im_le_norm _).trans hdiag
  have h3 : (baFMz sz z).eta n t * ‖(baFMz sz z).G n t ω x y‖ ^ 2 ≤ ((baFMz sz z).eta n t)⁻¹ := by
    calc _ ≤ (baFMz sz z).eta n t * ∑ w, ‖(baFMz sz z).G n t ω x w‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hη.le
      _ = _ := hw
      _ ≤ _ := h2
  set e := (baFMz sz z).eta n t with he
  by_contra hcon
  push Not at hcon
  have h4 : e⁻¹ < ‖(baFMz sz z).G n t ω x y‖ := hcon
  have h5 : 1 < e * ‖(baFMz sz z).G n t ω x y‖ := by
    have := mul_lt_mul_of_pos_left h4 hη
    rwa [mul_inv_cancel₀ hη.ne'] at this
  nlinarith [mul_pos hη hη, norm_nonneg ((baFMz sz z).G n t ω x y), inv_pos.2 hη, mul_inv_cancel₀ hη.ne']

end Carrier

/-! ## 4. The loop `𝓛^{(1)}` is the block average of the resolvent diagonal; `X_c = 𝓛^{(1)}_{+,c} - m` -/

section LoopOne

/-- `Gres (blockMat M) = (Gres M)` read on the block index (a copy of `Gres_blockMat'`, `Main/ZTransfer.lean:253`). -/
theorem BAExp14a_Gres_blockMat {d L W : ℕ} [NeZero L] [NeZero W] (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (s : Bool) :
    Gres (blockMat d L W M) z s = (Gres M z s).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold Gres
  generalize (if s then z else (starRingEnd ℂ) z) = w
  have h : blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - w • 1).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    simp [blockMat, Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]

/-- `tr(G E_c) = W^{-d} Σ_{x ∈ [c]} G_{xx}` for a fine matrix `G` read on the block index. -/
theorem BAExp14a_trace_Eblk {d L W : ℕ} [NeZero L] [NeZero W] (G : Matrix (Idx d L W) (Idx d L W) ℂ) (c : Zd d L) :
    Matrix.trace (G.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm * Eblk d L W c) =
      ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W c, G x x := by
  unfold Eblk
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_diagonal, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp (splitEquiv d L W)]
  simp only [Equiv.symm_apply_apply]
  have h1 : ∀ x : Idx d L W, G x x * (if (splitEquiv d L W x).1 = c then ((W : ℂ) ^ d)⁻¹ else 0) =
      ((W : ℂ) ^ d)⁻¹ * (if x ∈ Iblk d L W c then G x x else 0) := by
    intro x
    by_cases h : (split d L W x).1 = c
    · have hx : x ∈ Iblk d L W c := by simp [Iblk, h]
      have hx' : (splitEquiv d L W x).1 = c := h
      rw [if_pos hx', if_pos hx]; ring
    · have hx : x ∉ Iblk d L W c := by simp [Iblk, h]
      have hx' : ¬ (splitEquiv d L W x).1 = c := h
      rw [if_neg hx', if_neg hx]; simp
  simp only [h1, ← Finset.mul_sum]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ}

/-- **`𝓛^{(1)}_{+,c} = W^{-d} Σ_{x ∈ [c]} G_{xx}`** at the carrier. -/
theorem BAExp14a_L1_eq (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c : Zd d (sz.L n)) :
    (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).G n t ω x x := by
  change loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n t ω)
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) (fun _ : Fin 1 => true) (fun _ => c) = _
  unfold loopFine
  rw [loopM_eq_loopL]
  have h : loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n t ω))
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) (loopOf (fun _ : Fin 1 => true) (fun _ => c)) =
      Matrix.trace (Gres (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n t ω))
        (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t) true * Eblk d (sz.L n) (sz.W n) c) := by
    simp [loopL, loopOf, List.ofFn_succ]
  rw [h, BAExp14a_Gres_blockMat, BAExp14a_trace_Eblk]
  rfl

/-- **`X_c = 𝓛^{(1)}_{+,c} - m`** (`M_{vv} = m`, `Σ_{v ∈ [c]} 1 = W^d`). -/
theorem BAExp14a_X_eq (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)
    (hSelf : BASelf d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) ((baFMz sz z).m n)) (c : Zd d (sz.L n)) :
    BAExp14a_X sz z n t ω c = (baFMz sz z).L n t (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n := by
  rw [BAExp14a_L1_eq]
  unfold BAExp14a_X
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hM : ∀ v : Idx d (sz.L n) (sz.W n), (baFMz sz z).M n v v = (baFMz sz z).m n :=
    fun v => BAExpand_M_diag (BAflowLam0 sz z n) (BAflowEs sz z n) _ hSelf v
  have hsum : ∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).GM n t ω v v =
      ∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).G n t ω v v - ((sz.W n : ℕ) : ℂ) ^ d * (baFMz sz z).m n := by
    unfold FlowFM.GM
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_congr rfl fun v _ => hM v, Finset.sum_const, card_Iblk, nsmul_eq_mul]
    push_cast
    ring
  rw [hsum, mul_sub, ← mul_assoc, inv_mul_cancel₀ hW, one_mul]

end LoopOne

/-! ## 5. The random variables `a = max_c |X_c|`, `b = max_{x,y} |Ǧ_{xy}|` and their `≺` -/

section RandVar

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ}

/-- `a = max_c |X_c|`. -/
def BAExp14a_a (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨(0 : Zd d (sz.L n)), Finset.mem_univ _⟩ fun c : Zd d (sz.L n) => ‖BAExp14a_X sz z n t ω c‖

/-- `b = max_{x,y} |Ǧ_{xy}|`. -/
def BAExp14a_b (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Idx d (sz.L n) (sz.W n)), (0 : Idx d (sz.L n) (sz.W n))), Finset.mem_univ _⟩
    fun p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖(baFMz sz z).GM n t ω p.1 p.2‖

theorem BAExp14a_le_a (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (c : Zd d (sz.L n)) :
    ‖BAExp14a_X sz z n t ω c‖ ≤ BAExp14a_a sz z n t ω :=
  Finset.le_sup' (fun c : Zd d (sz.L n) => ‖BAExp14a_X sz z n t ω c‖) (Finset.mem_univ c)

theorem BAExp14a_le_b (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).GM n t ω x y‖ ≤ BAExp14a_b sz z n t ω :=
  Finset.le_sup' (fun p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖(baFMz sz z).GM n t ω p.1 p.2‖)
    (Finset.mem_univ (x, y))

theorem BAExp14a_a_nonneg (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : 0 ≤ BAExp14a_a sz z n t ω :=
  (norm_nonneg _).trans (BAExp14a_le_a n t ω 0)

theorem BAExp14a_b_nonneg (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : 0 ≤ BAExp14a_b sz z n t ω :=
  (norm_nonneg _).trans (BAExp14a_le_b n t ω 0 0)

theorem BAExp14a_exists_a (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    ∃ c : Zd d (sz.L n), BAExp14a_a sz z n t ω = ‖BAExp14a_X sz z n t ω c‖ := by
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_eq_sup' (⟨(0 : Zd d (sz.L n)), Finset.mem_univ _⟩ : (Finset.univ : Finset (Zd d (sz.L n))).Nonempty)
    (fun c : Zd d (sz.L n) => ‖BAExp14a_X sz z n t ω c‖)
  exact ⟨c, hc⟩

theorem BAExp14a_exists_b (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    ∃ x y : Idx d (sz.L n) (sz.W n), BAExp14a_b sz z n t ω = ‖(baFMz sz z).GM n t ω x y‖ := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup'
    (⟨((0 : Idx d (sz.L n) (sz.W n)), (0 : Idx d (sz.L n) (sz.W n))), Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))).Nonempty)
    (fun p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) => ‖(baFMz sz z).GM n t ω p.1 p.2‖)
  exact ⟨p.1, p.2, hp⟩

/-- `STWB ≤ B_{t,0}`: the profile decreases in the block distance. -/
theorem BAExp14a_STWB_le (n : ℕ) (t : ℝ) (K : ℕ) (ht1 : t < 1) : STWB sz n t K ≤ sz.Bctl n t := by
  unfold STWB Sizes.Bctl Bparam
  have hx : 0 < |1 - t| := abs_pos.2 (by linarith)
  have h1 : ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
  have h2 : (sz.lam n ^ 2 + |1 - t|)⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
      (sz.lam n ^ 2 + |1 - t|)⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    calc _ ≤ (sz.lam n ^ 2 + |1 - t|)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := mul_one _
  have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add h2 le_rfl) hW0

variable (μ : Measure sz.SeqΩ) (t : ℕ → ℝ)

/-- **`a ≺ B`** from `LWAvgLawgL` (`X_c = 𝓛^{(1)}_{+,c} - m`). -/
theorem BAExp14a_Dom_a {κ ε 𝔠 𝔡 : ℝ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hκ : 0 < κ)
    (hA : LWAvgLawgL (baFMz sz z) μ t) :
    BAExp14a_Dom sz μ (fun n ω => BAExp14a_a sz z n (t n) ω) (fun n => sz.Bctl n (t n)) := by
  unfold LWAvgLawgL PrecL at hA
  unfold BAExp14a_Dom PrecL
  refine BAExp14a_prec_of_bad hA fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨⟩, hu⟩ := hω
  obtain ⟨c, hc⟩ := BAExp14a_exists_a (sz := sz) (z := z) n (t n) ω
  refine ⟨c, ?_⟩
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  change ((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n (t n) < BAExp14a_a sz z n (t n) ω at hu
  change ((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n (t n) <
    ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => c) ω - (baFMz sz z).m n‖
  rw [← BAExp14a_X_eq n (t n) ω hr.1 c]
  rw [hc] at hu
  exact hu

/-- **`b ≺ B^{1/2}`** from `STLocalEntrygL` (`STWB ≤ B`, squares). -/
theorem BAExp14a_Dom_b {κ ε 𝔠 𝔡 : ℝ} (ht1 : ∀ n, t n < 1) (hE : STLocalEntrygL (baFMz sz z) μ t) :
    BAExp14a_Dom sz μ (fun n ω => BAExp14a_b sz z n (t n) ω) (fun n => (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) := by
  unfold STLocalEntrygL PrecL at hE
  unfold BAExp14a_Dom PrecL
  refine BAExp14a_prec_of_bad hE fun τ hτ => ⟨2 * τ, by positivity, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨⟩, hu⟩ := hω
  obtain ⟨x, y, hxy⟩ := BAExp14a_exists_b (sz := sz) (z := z) n (t n) ω
  refine ⟨(x, y), ?_⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hB0 : 0 ≤ sz.Bctl n (t n) := (STBctl_pos sz n (ht1 n)).le
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  change N ^ τ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) < BAExp14a_b sz z n (t n) ω at hu
  rw [hxy] at hu
  change N ^ (2 * τ) * STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) <
    ‖(baFMz sz z).GM n (t n) ω x y‖ ^ 2
  have h1 : 0 ≤ N ^ τ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hB0 _)
  have h2 : (N ^ τ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) ^ 2 < ‖(baFMz sz z).GM n (t n) ω x y‖ ^ 2 :=
    pow_lt_pow_left₀ hu h1 two_ne_zero
  have h3a : (N ^ τ) ^ 2 = N ^ (2 * τ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0, mul_comm]; norm_num
  have h3b : ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) ^ 2 = sz.Bctl n (t n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]; norm_num
  have h3 : (N ^ τ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) ^ 2 = N ^ (2 * τ) * sz.Bctl n (t n) := by
    rw [mul_pow, h3a, h3b]
  rw [h3] at h2
  refine lt_of_le_of_lt ?_ h2
  exact mul_le_mul_of_nonneg_left (BAExp14a_STWB_le n (t n) _ (ht1 n)) (Real.rpow_nonneg hN0 _)

end RandVar

/-! ## 6. The decomposition `F = F^Ǧ + F^M` and the pathwise bounds of the six families -/

section Families

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- The `Ǧ`-part of the closing edge: `Ǧ_{yx}` for `σ = true`, `\overline{Ǧ_{xy}}` for `σ = false`. -/
def BAExp14a_tailG (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then (baFMz sz z).GM n t ω y x else star ((baFMz sz z).GM n t ω x y)

/-- The `M`-part of the closing edge. -/
def BAExp14a_tailM (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then (baFMz sz z).M n y x else star ((baFMz sz z).M n x y)

/-- `J(x,y) = Σ_α X_{[α]} T(x,y,α)`. -/
def BAExp14a_Jx (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) * T x y α

/-- The kernels `T_k(x,y,α)` of the six families (order `F_MM, F_T1, F_T3A^{(0)}, F_T3A^{(1)}, F_C1, F_C2`). -/
def BAExp14a_T (k : Fin 6) :
    Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ :=
  ![fun x y α => (baFMz sz z).M n x α * (baFMz sz z).M n α y,
    fun x y α => ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n x β * (baFMz sz z).M n β y,
    fun x y α => ∑ w, ∑ γ, BAExp14a_Wk sz z n t false α w * (baFMz sz z).M n w γ *
      ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n γ)) * (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w,
    fun x y α => ∑ w, ∑ γ, BAExp14a_Wk sz z n t true α w * (baFMz sz z).M n w γ *
      ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n γ)) * (baFMz sz z).G n t ω γ y * (baFMz sz z).GM n t ω x w,
    fun x y α => ∑ α', (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) *
      (baFMz sz z).M n α α' * (baFMz sz z).G n t ω α' y,
    fun x y α => ∑ α', ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α')) * (baFMz sz z).M n x α' *
      (baFMz sz z).G n t ω α' α * (baFMz sz z).M n α y] k

/-- `F_k = outer (T_k)`. -/
theorem BAExp14a_F_eq (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14a_F sz z n t ω k σ a b = BAExp14a_outer sz z n t ω σ a b (BAExp14a_T sz z n t ω k) := by
  fin_cases k <;> rfl

/-- The `Ǧ`-part of `F_k`. -/
def BAExp14a_FG (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_frame a b (BAExp14a_tailG sz z n t ω σ) (BAExp14a_Jx sz z n t ω (BAExp14a_T sz z n t ω k))

/-- The `M`-part of `F_k`. -/
def BAExp14a_FM (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_frame a b (BAExp14a_tailM sz z n σ) (BAExp14a_Jx sz z n t ω (BAExp14a_T sz z n t ω k))

/-- **`F = F^Ǧ + F^M`** (`G = Ǧ + M`). -/
theorem BAExp14a_F_split (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14a_F sz z n t ω k σ a b = BAExp14a_FG sz z n t ω k σ a b + BAExp14a_FM sz z n t ω k σ a b := by
  rw [BAExp14a_F_eq]
  unfold BAExp14a_outer BAExp14a_FG BAExp14a_FM BAExp14a_frame BAExp14a_Jx
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← add_mul]
  congr 1
  unfold BAExp14a_tail BAExp14a_tailG BAExp14a_tailM FlowFM.GM
  cases σ
  · simp only [Bool.false_eq_true, ite_false, ← star_add, sub_add_cancel]
  · simp only [ite_true, sub_add_cancel]

end Families

section Pathwise

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t CM S : ℝ)

/-- **The deterministic facts at one size index `n` and one time `t`** (the hypotheses of the pathwise bounds): `0 ≤ t < 1`,
`0 < η ≤ 1`, the entries, rows, columns, offset support and ℓ² row of the fine `M`, the column sums of the weight kernels
`W^{(k)}` (`≤ S`), and the Ward identities of the resolvent. -/
structure BAExp14a_Facts : Prop where
  ht0 : 0 ≤ t
  ht1 : t < 1
  hη : 0 < (baFMz sz z).eta n t
  hη1 : (baFMz sz z).eta n t ≤ 1
  hCM : 0 ≤ CM
  hS : 1 ≤ S
  hM1 : ∀ x y, ‖(baFMz sz z).M n x y‖ ≤ 1
  hMr : ∀ x, ∑ y, ‖(baFMz sz z).M n x y‖ ≤ CM
  hMc : ∀ y, ∑ x, ‖(baFMz sz z).M n x y‖ ≤ CM
  hMo : ∀ x y, (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 → (baFMz sz z).M n x y = 0
  hMsq : ∀ x, ∑ y, ‖(baFMz sz z).M n x y‖ ^ 2 ≤ 1
  hWk : ∀ (k : Bool) (β : Idx d (sz.L n) (sz.W n)), ∑ α, ‖BAExp14a_Wk sz z n t k α β‖ ≤ S
  hwr : ∀ (ω : sz.SeqΩ) (x : Idx d (sz.L n) (sz.W n)),
    (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω x y‖ ^ 2 = ((baFMz sz z).G n t ω x x).im
  hwc : ∀ (ω : sz.SeqΩ) (x : Idx d (sz.L n) (sz.W n)),
    (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω y x‖ ^ 2 = ((baFMz sz z).G n t ω x x).im

variable {sz z n t CM S}

/-- The weight `K₃`-bound of the four pathwise families: `Jm = a² K₃ (1 + b)/η`, `K₃ = (5/2) S CM + CM²`. -/
def BAExp14a_Jm (η CM S a b : ℝ) : ℝ := a * (a * ((5 / 2 * S * CM + CM * CM) * ((1 + b) / η)))

theorem BAExp14a_Jm_nonneg {η CM S a b : ℝ} (hη : 0 < η) (hCM : 0 ≤ CM) (hS : 0 ≤ S) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ BAExp14a_Jm η CM S a b := by
  unfold BAExp14a_Jm; positivity

theorem BAExp14a_X_le_a (n : ℕ) (ω : sz.SeqΩ) (c : Zd d (sz.L n)) :
    ‖BAExp14a_X sz z n t ω c‖ ≤ BAExp14a_a sz z n t ω := BAExp14a_le_a n t ω c

/-- **The pathwise sums of the four non-linear families** `k ∈ {T3A⁰, T3A¹, C1, C2}`: `|J_k(x,y)| ≤ a² K₃ (1 + b)/η`. -/
theorem BAExp14a_J_path_le (hf : BAExp14a_Facts sz z n t CM S) (ω : sz.SeqΩ) (k : Fin 6) (hk : 2 ≤ k.val)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖BAExp14a_Jx sz z n t ω (BAExp14a_T sz z n t ω k) x y‖ ≤
      BAExp14a_Jm ((baFMz sz z).eta n t) CM S (BAExp14a_a sz z n t ω) (BAExp14a_b sz z n t ω) := by
  have ha : ∀ c, ‖BAExp14a_X sz z n t ω c‖ ≤ BAExp14a_a sz z n t ω := fun c => BAExp14a_le_a n t ω c
  have hb : ∀ x y, ‖(baFMz sz z).GM n t ω x y‖ ≤ BAExp14a_b sz z n t ω := fun x y => BAExp14a_le_b n t ω x y
  have hG : ∀ x y, (baFMz sz z).G n t ω x y = (baFMz sz z).M n x y + (baFMz sz z).GM n t ω x y := fun x y => by
    unfold FlowFM.GM; ring
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg hf.ht0]; exact hf.ht1.le
  have ha0 := BAExp14a_a_nonneg (sz := sz) (z := z) n t ω
  have hb0 := BAExp14a_b_nonneg (sz := sz) (z := z) n t ω
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  have hone : (1 : ℝ) ≤ (1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t := by
    rw [le_div_iff₀ hf.hη]; linarith [hf.hη1]
  have hgb : ∀ x y, ‖(baFMz sz z).G n t ω x y‖ ≤ 1 + BAExp14a_b sz z n t ω := fun x y => by
    rw [hG x y]; exact (norm_add_le _ _).trans (add_le_add (hf.hM1 x y) (hb x y))
  have hu : 1 + BAExp14a_b sz z n t ω ≤ (1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t := by
    rw [le_div_iff₀ hf.hη]; nlinarith [hf.hη1]
  have hK : CM * CM ≤ 5 / 2 * S * CM + CM * CM := by nlinarith [mul_nonneg hS0 hf.hCM]
  have hC : (1 + BAExp14a_b sz z n t ω) * (CM * CM) ≤
      (5 / 2 * S * CM + CM * CM) * ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t) := by
    calc (1 + BAExp14a_b sz z n t ω) * (CM * CM) ≤ ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t) * (5 / 2 * S * CM + CM * CM) :=
          mul_le_mul hu hK (mul_self_nonneg _) (by linarith)
      _ = _ := by ring
  unfold BAExp14a_Jx
  fin_cases k
  · simp at hk
  · simp at hk
  · -- T3A⁰
    have h := BAExp14a_J_T3A_bd (fun c => BAExp14a_X sz z n t ω c) (BAExp14a_Wk sz z n t false) ((baFMz sz z).M n)
      ((baFMz sz z).G n t ω) ((baFMz sz z).GM n t ω) ha ht1 (fun β => hf.hWk false β) hf.hMr hf.hMc hf.hM1 hf.hMsq hG hb
      hf.hη hf.hη1 (hf.hwr ω) (hf.hwc ω) x y
    refine h.trans ?_
    unfold BAExp14a_Jm
    gcongr
    nlinarith [mul_nonneg hS0 hf.hCM, mul_nonneg hf.hCM hf.hCM, hone]
  · have h := BAExp14a_J_T3A_bd (fun c => BAExp14a_X sz z n t ω c) (BAExp14a_Wk sz z n t true) ((baFMz sz z).M n)
      ((baFMz sz z).G n t ω) ((baFMz sz z).GM n t ω) ha ht1 (fun β => hf.hWk true β) hf.hMr hf.hMc hf.hM1 hf.hMsq hG hb
      hf.hη hf.hη1 (hf.hwr ω) (hf.hwc ω) x y
    refine h.trans ?_
    unfold BAExp14a_Jm
    gcongr
    nlinarith [mul_nonneg hS0 hf.hCM, mul_nonneg hf.hCM hf.hCM, hone]
  · have h := BAExp14a_J_C1_le (fun c => BAExp14a_X sz z n t ω c) ((baFMz sz z).M n) ((baFMz sz z).G n t ω) ha ht1 hf.hMr hgb x y
    refine h.trans ?_
    unfold BAExp14a_Jm
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC ha0) ha0
  · have h := BAExp14a_J_C2_le (fun c => BAExp14a_X sz z n t ω c) ((baFMz sz z).M n) ((baFMz sz z).G n t ω) ha ht1 hf.hMr hf.hMc hgb x y
    refine h.trans ?_
    unfold BAExp14a_Jm
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC ha0) ha0

theorem BAExp14a_tailG_le (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖BAExp14a_tailG sz z n t ω σ x y‖ ≤ BAExp14a_b sz z n t ω := by
  unfold BAExp14a_tailG
  cases σ
  · simp only [Bool.false_eq_true, ite_false, norm_star]; exact BAExp14a_le_b n t ω x y
  · simp only [ite_true]; exact BAExp14a_le_b n t ω y x

theorem BAExp14a_tailM_le (hf : BAExp14a_Facts sz z n t CM S) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖BAExp14a_tailM sz z n σ x y‖ ≤ 1 := by
  unfold BAExp14a_tailM
  cases σ
  · simp only [Bool.false_eq_true, ite_false, norm_star]; exact hf.hM1 x y
  · simp only [ite_true]; exact hf.hM1 y x

theorem BAExp14a_tailM_supp (hf : BAExp14a_Facts sz z n t CM S) (σ : Bool) (x y : Idx d (sz.L n) (sz.W n))
    (hxy : (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2) :
    BAExp14a_tailM sz z n σ x y = 0 := by
  unfold BAExp14a_tailM
  cases σ
  · simp only [Bool.false_eq_true, ite_false, star_eq_zero]; exact hf.hMo x y hxy
  · simp only [ite_true]; exact hf.hMo y x (fun h => hxy h.symm)

/-- For the two linear families `k ∈ {MM, T1}` the kernel is `Σ_β Wk_{αβ} M_{xβ} M_{βy}` with `Wk = 1` (`MM`) or `W - 1` (`T1`). -/
theorem BAExp14a_T_lin_eq (k : Fin 6) (hk : k.val < 2) (x y α : Idx d (sz.L n) (sz.W n)) :
    BAExp14a_T sz z n t ω k x y α = ∑ β, BAExp14a_Wk sz z n t (decide (k.val = 1)) α β * (baFMz sz z).M n x β *
      (baFMz sz z).M n β y := by
  fin_cases k
  · simp only [BAExp14a_T, BAExp14a_Wk]
    simp [Matrix.one_apply]
  · simp [BAExp14a_T]
  · simp at hk
  · simp at hk
  · simp at hk
  · simp at hk

theorem BAExp14a_T_lin_l1 (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : k.val < 2)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ∑ α, ‖BAExp14a_T sz z n t ω k x y α‖ ≤ S * CM := by
  simp only [BAExp14a_T_lin_eq k hk]
  exact BAExp14a_T_MM_l1 _ _ (hf.hWk _) hf.hM1 hf.hMr x y

theorem BAExp14a_T_lin_supp (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : k.val < 2)
    (x y : Idx d (sz.L n) (sz.W n)) (hxy : (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2)
    (α : Idx d (sz.L n) (sz.W n)) : BAExp14a_T sz z n t ω k x y α = 0 := by
  rw [BAExp14a_T_lin_eq k hk]
  exact BAExp14a_T_MM_supp _ _ hf.hMo x y hxy α

theorem BAExp14a_J_lin_le (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : k.val < 2)
    (x y : Idx d (sz.L n) (sz.W n)) :
    ‖BAExp14a_Jx sz z n t ω (BAExp14a_T sz z n t ω k) x y‖ ≤ BAExp14a_a sz z n t ω * (S * CM) :=
  (BAExp14a_sum_X_le (fun c => BAExp14a_X sz z n t ω c) _ (fun c => BAExp14a_le_a n t ω c)).trans
    (mul_le_mul_of_nonneg_left (BAExp14a_T_lin_l1 hf k hk x y) (BAExp14a_a_nonneg n t ω))

theorem BAExp14a_J_lin_supp (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : k.val < 2)
    (x y : Idx d (sz.L n) (sz.W n)) (hxy : (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2) :
    BAExp14a_Jx sz z n t ω (BAExp14a_T sz z n t ω k) x y = 0 := by
  unfold BAExp14a_Jx
  exact Finset.sum_eq_zero fun α _ => by rw [BAExp14a_T_lin_supp hf k hk x y hxy α, mul_zero]

/-- `‖F^Ǧ_k‖ ≤ b · Jm` for the four pathwise families. -/
theorem BAExp14a_FG_path_le (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : 2 ≤ k.val) (σ : Bool)
    (a b : Zd d (sz.L n)) :
    ‖BAExp14a_FG sz z n t ω k σ a b‖ ≤ BAExp14a_b sz z n t ω *
      BAExp14a_Jm ((baFMz sz z).eta n t) CM S (BAExp14a_a sz z n t ω) (BAExp14a_b sz z n t ω) := by
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  exact BAExp14a_frame_le_full a b _ _ (fun x y => BAExp14a_tailG_le σ x y) (fun x y => BAExp14a_J_path_le hf ω k hk x y)
    (BAExp14a_b_nonneg n t ω) (BAExp14a_Jm_nonneg hf.hη hf.hCM hS0 (BAExp14a_a_nonneg n t ω) (BAExp14a_b_nonneg n t ω))

/-- `‖F^M_k‖ ≤ W^{-d} Jm` for the four pathwise families. -/
theorem BAExp14a_FM_path_le (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : 2 ≤ k.val) (σ : Bool)
    (a b : Zd d (sz.L n)) :
    ‖BAExp14a_FM sz z n t ω k σ a b‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      BAExp14a_Jm ((baFMz sz z).eta n t) CM S (BAExp14a_a sz z n t ω) (BAExp14a_b sz z n t ω) := by
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  unfold BAExp14a_FM
  have h := BAExp14a_frame_le_diag a b _ _ (fun x y => BAExp14a_tailM_le hf σ x y)
    (fun x y => BAExp14a_J_path_le hf ω k hk x y) zero_le_one
    (BAExp14a_Jm_nonneg hf.hη hf.hCM hS0 (BAExp14a_a_nonneg n t ω) (BAExp14a_b_nonneg n t ω)) (by
      intro x y hxy
      rw [BAExp14a_tailM_supp hf σ x y hxy, zero_mul])
  simpa only [one_mul] using h

/-- `‖F^Ǧ_k‖ ≤ W^{-d} b a S CM` for the two linear families. -/
theorem BAExp14a_FG_lin_le (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : k.val < 2) (σ : Bool)
    (a b : Zd d (sz.L n)) :
    ‖BAExp14a_FG sz z n t ω k σ a b‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      (BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (S * CM))) := by
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  refine BAExp14a_frame_le_diag a b _ _ (fun x y => BAExp14a_tailG_le σ x y)
    (fun x y => BAExp14a_J_lin_le hf k hk x y) (BAExp14a_b_nonneg n t ω)
    (mul_nonneg (BAExp14a_a_nonneg n t ω) (mul_nonneg hS0 hf.hCM)) ?_
  intro x y hxy
  rw [BAExp14a_J_lin_supp hf k hk x y hxy, mul_zero]

/-- `‖F^M_k‖ ≤ W^{-d} a S CM` for the two linear families (pathwise, the crude bound used for the envelope). -/
theorem BAExp14a_FM_lin_le (hf : BAExp14a_Facts sz z n t CM S) (k : Fin 6) (hk : k.val < 2) (σ : Bool)
    (a b : Zd d (sz.L n)) :
    ‖BAExp14a_FM sz z n t ω k σ a b‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BAExp14a_a sz z n t ω * (S * CM)) := by
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  unfold BAExp14a_FM
  have h := BAExp14a_frame_le_diag a b _ _ (fun x y => BAExp14a_tailM_le hf σ x y)
    (fun x y => BAExp14a_J_lin_le hf k hk x y) zero_le_one
    (mul_nonneg (BAExp14a_a_nonneg n t ω) (mul_nonneg hS0 hf.hCM)) (by
      intro x y hxy
      rw [BAExp14a_tailM_supp hf σ x y hxy, zero_mul])
  simpa only [one_mul] using h

end Pathwise

/-! ## 7. The facts along the flow -/

section FactsFlow

/-- **The deterministic facts hold along the flow** for `n` large and every `t ∈ [0, t₀]`, with constants `CM`, `S` depending on
`(k, 𝔡, κ)` only (`Λ = 𝔡⁻¹`, `d = k + 2`); no smallness of `g` (C1, 2149 L5). -/
theorem BAExp14a_facts_of_flow {k : ℕ} (hk : 1 ≤ k) {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ)
    (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) :
    ∃ CM S : ℝ, 0 ≤ CM ∧ 1 ≤ S ∧ ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t ≤ BAflowT0 sz z n →
      BAExp14a_Facts sz z n t CM S := by
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨CM, hCMpos, hCM⟩ := BAExp14a_M_row_l1 (k := k) hΛ hκ
  obtain ⟨Sω, hSω, hθ⟩ := BAExp14a_theta_l1 hk hΛ hκ
  refine ⟨CM, Sω + 1, hCMpos.le, by linarith, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn t ht0 ht
  obtain ⟨hg0, hgΛ⟩ := hn
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  obtain ⟨ht1, -, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hm1 : ‖(baFMz sz z).m n‖ ≤ 1 :=
    BAm_norm_le_one (k + 2) (sz.L n) _ _ _ (by simp) hr.1
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  refine ⟨ht0, ht1, hη, ?_, hCMpos.le, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- η ≤ 1
    rw [BAExp14a_eta_eq]
    unfold etaOf
    have h1 : ((baFMz sz z).m n).im ≤ 1 := (Complex.im_le_norm _).trans hm1
    have h2 : 1 - t ≤ 1 := by linarith
    have h3 : 0 ≤ 1 - t := by linarith
    nlinarith [mul_le_mul h2 h1 hmi.le zero_le_one]
  · exact fun x y => BAExp14a_M_le_one hr.1 x y
  · exact fun x => hCM (sz.L n) (sz.W n) hL _ _ _ hg0 hgΛ hr x
  · intro y
    have := BAExp14a_M_col_eq (W := sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) ((baFMz sz z).m n) y
    exact this.trans_le (hCM (sz.L n) (sz.W n) hL _ _ _ hg0 hgΛ hr y)
  · exact fun x y hxy => BAExp14a_M_supp hr.1 x y hxy
  · intro x
    exact (baM_row_sq (k + 2) (sz.L n) (sz.W n) _ _ _ hr.1 x).le
  · intro b β
    cases b
    · have : ∑ α : Idx (k + 2) (sz.L n) (sz.W n), ‖BAExp14a_Wk sz z n t false α β‖ = 1 := by
        simp [BAExp14a_Wk, Matrix.one_apply, apply_ite norm]
      rw [this]; linarith
    · exact BAExp14a_Wsub_col hL hr ht0 ht1
        (BAExp14a_theta_col hr ht0 ht1 (fun x => hθ (sz.L n) hL _ hg0 hgΛ _ _ hr t ht0 ht1 x)) β
  · exact fun ω x => (BAExp14a_G_ward hκ hflow n ht0 ht ω x).1
  · exact fun ω x => (BAExp14a_G_ward hκ hflow n ht0 ht ω x).2

end FactsFlow

/-! ## 8. `𝔼 X_c`: `lanlw` with `f = 1` (`B:359-372`), then the Neumann bound -/

/-- The law of the block Anderson model, `seqP (sz.withLam 0)`, read on `sz.SeqΩ` (the two sample spaces are definitionally equal,
not reducibly). -/
abbrev BAExp14a_μ {d : ℕ} (sz : Sizes d) : Measure sz.SeqΩ := Sizes.seqP (sz.withLam 0)

instance BAExp14a_inst_prob {d : ℕ} (sz : Sizes d) : IsProbabilityMeasure (BAExp14a_μ sz) :=
  Sizes.isProbabilityMeasure_seqP (sz.withLam 0)

section Lanlw

/-- `S^{(B)}(0) = I`. -/
private theorem BAExp14a_SB_zero {d L : ℕ} [NeZero L] : SB d L (0 : ℝ) = (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
  ext a b
  rw [SB_apply]
  by_cases h : a = b
  · subst h; simp [sbKernel]
  · have : a - b ≠ 0 := sub_ne_zero.mpr h
    simp [sbKernel, this, h]

/-- `S_{αβ} = t W^{-d} 1([α] = [β])` (`BAlwS`, `S^{(B)}(0) = I`). -/
theorem BAExp14a_S_apply {d L W : ℕ} [NeZero L] [NeZero W] (t : ℝ) (α β : Idx d L W) :
    BAlwS d L W t α β = (t : ℂ) * (((W : ℂ) ^ d)⁻¹ * if (split d L W α).1 = (split d L W β).1 then 1 else 0) := by
  have h : Matrix.of (BAlwS d L W t) = lwSmat d L W 0 t := by
    ext x y
    simp [BAlwS, lwSmat]
  have := congrFun (congrFun h α) β
  rw [Matrix.of_apply] at this
  rw [this, lwSmat_eq, BAExp14a_SB_zero]
  simp [lwLift, Matrix.one_apply]

theorem BAExp14a_lwf_one {d L W : ℕ} [NeZero L] [NeZero W] {g0 E t : ℝ} {m : ℂ} (ω : Ω d L W) :
    BAlwf d L W g0 E t m 1 ω = 1 := by
  simp [BAlwf, LWPins_resPoly]

theorem BAExp14a_lwdf_one {d L W : ℕ} [NeZero L] [NeZero W] {g0 E t : ℝ} {m : ℂ} (ω : Ω d L W) (α w : Idx d L W) :
    BAlwdf d L W g0 E t m 1 ω α w = 0 := by
  simp [BAlwdf, LWPins_dH, LWPins_resPoly]

theorem BAExp14a_cont_lwG {d L W : ℕ} [NeZero L] [NeZero W] {g0 E t : ℝ} {m : ℂ} (hz : (ztOf m E t).im ≠ 0)
    (x y : Idx d L W) : Continuous fun ω : Ω d L W => BAlwG d L W g0 E t m ω x y := by
  have h : Continuous fun ω : Ω d L W => Gres (BAlwH d L W g0 t ω) (ztOf m E t) true := by
    refine Gauss.continuous_green_of_isHermitian ?_ (fun ω => ?_) hz
    · exact continuous_const.add (continuous_Hflow d L W t)
    · have h1 : ((g0 : ℂ) • PsiI d L W).IsHermitian := by
        unfold IsHermitian
        rw [conjTranspose_smul, (PsiI_isHermitian d L W).eq, show star (g0 : ℂ) = (g0 : ℂ) from Complex.conj_ofReal _]
      exact h1.add (Hflow_isHermitian d L W t ω)
  exact (continuous_apply y).comp ((continuous_apply x).comp h)

/-- The coordinates of the common sample space at size `n`, typed as a sample of `PF d (L n) (W n) 0`
(`Sizes.slice (sz.withLam 0) n`). -/
def BAExp14a_slc {d : ℕ} (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) : Ω d (sz.L n) (sz.W n) :=
  Sizes.slice (sz.withLam 0) n ω

/-- `∫ Φ ∘ slice ∂seqP(sz.withLam 0) = ∫ Φ ∂PF d L W 0` for continuous `Φ`. -/
theorem BAExp14a_int_slice {d : ℕ} {sz : Sizes d} (n : ℕ) (Φ : Ω d (sz.L n) (sz.W n) → ℂ) (hΦ : Continuous Φ) :
    ∫ ω, Φ (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) = ∫ ω', Φ ω' ∂(PF d (sz.L n) (sz.W n) 0) := by
  have hmap := Sizes.seqP_map_slice (sz.withLam 0) n
  change ∫ ω, Φ (Sizes.slice (sz.withLam 0) n ω) ∂(Sizes.seqP (sz.withLam 0)) = _
  rw [← integral_map (Sizes.measurable_slice (sz.withLam 0) n).aemeasurable hΦ.aestronglyMeasurable]
  congr 1

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ}

/-- `Σ_β S_{αβ} Ǧ_{ββ} = t X_{[α]}`. -/
theorem BAExp14a_sumS_GM (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (α : Idx d (sz.L n) (sz.W n)) :
    ∑ β, BAlwS d (sz.L n) (sz.W n) t α β * (baFMz sz z).GM n t ω β β =
      (t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α) := by
  unfold BAExp14a_X
  simp only [BAExp14a_S_apply]
  have h : ∀ β : Idx d (sz.L n) (sz.W n),
      (t : ℂ) * (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) * (if (split d (sz.L n) (sz.W n) α).1 = (split d (sz.L n) (sz.W n) β).1 then 1 else 0)) *
        (baFMz sz z).GM n t ω β β =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (if β ∈ Iblk d (sz.L n) (sz.W n) (STblk sz n α) then (baFMz sz z).GM n t ω β β else 0)) := by
    intro β
    have hmem : β ∈ Iblk d (sz.L n) (sz.W n) (STblk sz n α) ↔ (split d (sz.L n) (sz.W n) α).1 = (split d (sz.L n) (sz.W n) β).1 := by
      simp [Iblk, STblk, eq_comm]
    by_cases hb : β ∈ Iblk d (sz.L n) (sz.W n) (STblk sz n α)
    · rw [if_pos hb, if_pos (hmem.1 hb)]; ring
    · rw [if_neg hb, if_neg (fun h' => hb (hmem.2 h'))]; ring
  simp only [h, ← Finset.mul_sum]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **`lanlw` with `f = 1`, `y = x`**, at the carrier: `𝔼 Ǧ_{xx} = 𝔼 Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αx}` (the transport of
`baLanlw_holds` from `PF d L W 0` to the sample space of `seqP (sz.withLam 0)`). -/
theorem BAExp14a_lanlw_diag (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (x : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (baFMz sz z).GM n t ω x x ∂(BAExp14a_μ sz) =
      ∫ ω, ∑ α, (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α)) * (baFMz sz z).G n t ω α x
        ∂(BAExp14a_μ sz) := by
  obtain ⟨ht1, hr, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hz : (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im ≠ 0 := hzi.ne'
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have key := baLanlw_holds d (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hSelf ht0 ht1 1 x x
  have cG : ∀ α β : Idx d (sz.L n) (sz.W n), Continuous fun ω' : Ω d (sz.L n) (sz.W n) =>
      BAlwG d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) ω' α β :=
    fun α β => BAExp14a_cont_lwG hz α β
  have cL : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x ω' := by
    simp only [BAlanlwL, BAlwGc, BAExp14a_lwf_one, mul_one]
    exact (cG x x).sub continuous_const
  have cR : Continuous fun ω' : Ω d (sz.L n) (sz.W n) => BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x ω' := by
    simp only [BAlanlwR, BAlwGc, BAExp14a_lwf_one, BAExp14a_lwdf_one, mul_one, mul_zero, Finset.sum_const_zero, sub_zero]
    have := cG
    fun_prop
  have eL : ∀ ω : sz.SeqΩ, (baFMz sz z).GM n t ω x x = BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n)
      (BAflowEs sz z n) t (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x (BAExp14a_slc sz n ω) := by
    intro ω
    unfold BAlanlwL
    rw [BAExp14a_lwf_one (BAExp14a_slc sz n ω), mul_one]
    rfl
  have eR : ∀ ω : sz.SeqΩ, ∑ α, (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α)) *
      (baFMz sz z).G n t ω α x = BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x (BAExp14a_slc sz n ω) := by
    intro ω
    unfold BAlanlwR
    simp only [BAExp14a_lwf_one (BAExp14a_slc sz n ω), BAExp14a_lwdf_one (BAExp14a_slc sz n ω),
      mul_one, mul_zero, Finset.sum_const_zero, sub_zero]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← BAExp14a_sumS_GM n t ω α]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    show (baFMz sz z).M n x α * (BAlwS d (sz.L n) (sz.W n) t α β * (baFMz sz z).GM n t ω β β) * (baFMz sz z).G n t ω α x =
      (baFMz sz z).M n x α * BAlwS d (sz.L n) (sz.W n) t α β * (baFMz sz z).GM n t ω β β * (baFMz sz z).G n t ω α x
    ring
  calc ∫ ω, (baFMz sz z).GM n t ω x x ∂(BAExp14a_μ sz)
      = ∫ ω, BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x (BAExp14a_slc sz n ω)
          ∂(BAExp14a_μ sz) := integral_congr_ae (Eventually.of_forall eL)
    _ = ∫ ω', BAlanlwL d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x ω' ∂(PF d (sz.L n) (sz.W n) 0) :=
        BAExp14a_int_slice n _ cL
    _ = ∫ ω', BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x ω' ∂(PF d (sz.L n) (sz.W n) 0) := key
    _ = ∫ ω, BAlanlwR d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) 1 x x (BAExp14a_slc sz n ω)
          ∂(BAExp14a_μ sz) := (BAExp14a_int_slice n _ cR).symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun ω => (eR ω).symm)

/-! ### Continuity, bounds, integrability of the basic random variables -/

theorem BAExp14a_cont_G (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (x y : Idx d (sz.L n) (sz.W n)) :
    Continuous fun ω : sz.SeqΩ => (baFMz sz z).G n t ω x y := by
  obtain ⟨-, -, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have h : Continuous fun ω : sz.SeqΩ => Gres (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω)
      (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) true := by
    refine Gauss.continuous_green_of_isHermitian ?_ (fun ω => BAExpand_Hm_isHermitian sz n _ t ω) hzi.ne'
    exact continuous_const.add (Green.GreenDeriv_continuous_seqHflow sz n t)
  exact (continuous_apply y).comp ((continuous_apply x).comp h)

theorem BAExp14a_cont_GM (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (x y : Idx d (sz.L n) (sz.W n)) :
    Continuous fun ω : sz.SeqΩ => (baFMz sz z).GM n t ω x y :=
  (BAExp14a_cont_G hκ hflow n ht0 ht x y).sub continuous_const

theorem BAExp14a_cont_X (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) (c : Zd d (sz.L n)) :
    Continuous fun ω : sz.SeqΩ => BAExp14a_X sz z n t ω c := by
  have := fun x y => BAExp14a_cont_GM hκ hflow n ht0 ht x y
  unfold BAExp14a_X
  fun_prop

/-- `|Ǧ_{xy}| ≤ η⁻¹ + 1` pathwise (`|G| ≤ η⁻¹`, `|M| ≤ 1`). -/
theorem BAExp14a_GM_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ} (hf : BAExp14a_Facts sz z n t CM S) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).GM n t ω x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := by
  unfold FlowFM.GM
  exact (norm_sub_le _ _).trans (add_le_add (BAExp14a_G_le hκ hflow n ht0 ht ω x y) (hf.hM1 x y))

/-- `|X_c| ≤ η⁻¹ + 1`. -/
theorem BAExp14a_X_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ} (hf : BAExp14a_Facts sz z n t CM S) (ω : sz.SeqΩ) (c : Zd d (sz.L n)) :
    ‖BAExp14a_X sz z n t ω c‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := by
  unfold BAExp14a_X
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (baFMz sz z).GM n t ω v v‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ v ∈ Iblk d (sz.L n) (sz.W n) c, (((baFMz sz z).eta n t)⁻¹ + 1) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => BAExp14a_GM_le hκ hflow n ht0 ht hf ω v v))
          (by positivity)
    _ = ((baFMz sz z).eta n t)⁻¹ + 1 := by
        rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]
        push_cast
        field_simp

theorem BAExp14a_integrable {f : sz.SeqΩ → ℂ} (hf : Continuous f) {C : ℝ} (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable f (BAExp14a_μ sz) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

section ExpX

variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
  (hf : BAExp14a_Facts sz z n t CM S)
include hκ hflow ht0 ht hf

theorem BAExp14a_int_GM (x y : Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => (baFMz sz z).GM n t ω x y) (BAExp14a_μ sz) :=
  BAExp14a_integrable (BAExp14a_cont_GM hκ hflow n ht0 ht x y) (fun ω => BAExp14a_GM_le hκ hflow n ht0 ht hf ω x y)

theorem BAExp14a_int_X (c : Zd d (sz.L n)) :
    Integrable (fun ω => BAExp14a_X sz z n t ω c) (BAExp14a_μ sz) :=
  BAExp14a_integrable (BAExp14a_cont_X hκ hflow n ht0 ht c) (fun ω => BAExp14a_X_le hκ hflow n ht0 ht hf ω c)

theorem BAExp14a_int_XGM (c : Zd d (sz.L n)) (y w : Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => BAExp14a_X sz z n t ω c * (baFMz sz z).GM n t ω y w) (BAExp14a_μ sz) := by
  refine BAExp14a_integrable ((BAExp14a_cont_X hκ hflow n ht0 ht c).mul (BAExp14a_cont_GM hκ hflow n ht0 ht y w))
    (C := (((baFMz sz z).eta n t)⁻¹ + 1) * (((baFMz sz z).eta n t)⁻¹ + 1)) fun ω => ?_
  rw [norm_mul]
  exact mul_le_mul (BAExp14a_X_le hκ hflow n ht0 ht hf ω c) (BAExp14a_GM_le hκ hflow n ht0 ht hf ω y w) (norm_nonneg _)
    (by have := hf.hη; positivity)

end ExpX

/-- `e_c = 𝔼 X_c`. -/
def BAExp14a_e (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (c : Zd d (sz.L n)) : ℂ :=
  ∫ ω, BAExp14a_X sz z n t ω c ∂(BAExp14a_μ sz)

/-- `q_{c,y,w} = 𝔼 [X_c Ǧ_{yw}]`. -/
def BAExp14a_q (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (c : Zd d (sz.L n)) (y w : Idx d (sz.L n) (sz.W n)) : ℂ :=
  ∫ ω, BAExp14a_X sz z n t ω c * (baFMz sz z).GM n t ω y w ∂(BAExp14a_μ sz)

section ExpX2

variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
  (hf : BAExp14a_Facts sz z n t CM S)
include hκ hflow ht0 ht hf

/-- `𝔼 Ǧ_{xx} = Σ_α (M_{xα} t M_{αx} e_{[α]} + M_{xα} t q_{[α],α,x})` (`lanlw`, `G = M + Ǧ`). -/
theorem BAExp14a_EGxx (x : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (baFMz sz z).GM n t ω x x ∂(BAExp14a_μ sz) =
      ∑ α, (((baFMz sz z).M n x α * (t : ℂ) * (baFMz sz z).M n α x) * BAExp14a_e sz z n t (STblk sz n α) +
        ((baFMz sz z).M n x α * (t : ℂ)) * BAExp14a_q sz z n t (STblk sz n α) α x) := by
  rw [BAExp14a_lanlw_diag hκ hflow n ht0 ht x]
  have hpt : ∀ ω : sz.SeqΩ, ∑ α, (baFMz sz z).M n x α * ((t : ℂ) * BAExp14a_X sz z n t ω (STblk sz n α)) *
      (baFMz sz z).G n t ω α x = ∑ α, (((baFMz sz z).M n x α * (t : ℂ) * (baFMz sz z).M n α x) *
        BAExp14a_X sz z n t ω (STblk sz n α) + ((baFMz sz z).M n x α * (t : ℂ)) *
          (BAExp14a_X sz z n t ω (STblk sz n α) * (baFMz sz z).GM n t ω α x)) := by
    intro ω
    refine Finset.sum_congr rfl fun α _ => ?_
    have : (baFMz sz z).G n t ω α x = (baFMz sz z).M n α x + (baFMz sz z).GM n t ω α x := by
      unfold FlowFM.GM; ring
    rw [this]; ring
  simp only [hpt]
  rw [integral_finset_sum _ fun α _ => ?_]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_add, integral_const_mul, integral_const_mul]
    · rfl
    · exact (BAExp14a_int_X hκ hflow n ht0 ht hf _).const_mul _
    · exact (BAExp14a_int_XGM hκ hflow n ht0 ht hf _ _ _).const_mul _
  · exact ((BAExp14a_int_X hκ hflow n ht0 ht hf _).const_mul _).add
      ((BAExp14a_int_XGM hκ hflow n ht0 ht hf _ _ _).const_mul _)

end ExpX2

/-- The block matrix `M^{(B)}` at the flow data. -/
abbrev BAExp14a_MB (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  BAMB d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)

/-- `R_c = t W^{-d} Σ_{x ∈ [c]} Σ_α M_{xα} q_{[α],α,x}`. -/
def BAExp14a_R (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (c : Zd d (sz.L n)) : ℂ :=
  (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, ∑ α,
    (baFMz sz z).M n x α * BAExp14a_q sz z n t (STblk sz n α) α x)

/-- The fibre sum of the `M`-part: for `x ∈ [c]`, `Σ_α M_{xα} t M_{αx} e_{[α]} = t Σ_b (M^{(B)}_{cb})² e_b`. -/
theorem BAExp14a_sumA (hmi : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) (t : ℝ) (e : Zd d (sz.L n) → ℂ)
    (x : Idx d (sz.L n) (sz.W n)) :
    ∑ α, ((baFMz sz z).M n x α * (t : ℂ) * (baFMz sz z).M n α x) * e (STblk sz n α) =
      (t : ℂ) * ∑ b, (BAExp14a_MB sz z n (split d (sz.L n) (sz.W n) x).1 b) ^ 2 * e b := by
  have h1 : ∀ α : Idx d (sz.L n) (sz.W n),
      ((baFMz sz z).M n x α * (t : ℂ) * (baFMz sz z).M n α x) * e (STblk sz n α) =
      if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) α).2 then
        (fun b => (t : ℂ) * ((BAExp14a_MB sz z n (split d (sz.L n) (sz.W n) x).1 b) ^ 2 * e b)) (split d (sz.L n) (sz.W n) α).1
      else 0 := by
    intro α
    have hxa := BAMfine_eq sz (BAflowLam0 sz z) (BAflowEs sz z) n hmi x α
    have hax := BAMfine_eq sz (BAflowLam0 sz z) (BAflowEs sz z) n hmi α x
    change ((BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n x α) * (t : ℂ) * BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n α x) *
      e (split d (sz.L n) (sz.W n) α).1 = _
    rw [hxa, hax]
    by_cases ho : (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) α).2
    · have ho' : (split d (sz.L n) (sz.W n) α).2 = (split d (sz.L n) (sz.W n) x).2 := ho.symm
      rw [if_pos ho, if_pos ho', if_pos ho]
      have hs := BAMB_symm d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (split d (sz.L n) (sz.W n) α).1 (split d (sz.L n) (sz.W n) x).1
      rw [hs]; ring
    · have ho' : ¬ (split d (sz.L n) (sz.W n) α).2 = (split d (sz.L n) (sz.W n) x).2 := fun e => ho e.symm
      rw [if_neg ho, if_neg ho', if_neg ho]; simp
  simp only [h1]
  rw [BASizeClaim_fibre_sum x (fun b => (t : ℂ) * ((BAExp14a_MB sz z n (split d (sz.L n) (sz.W n) x).1 b) ^ 2 * e b)),
    Finset.mul_sum]

section ExpX3

variable (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
  (hf : BAExp14a_Facts sz z n t CM S)
include hκ hflow ht0 ht hf

/-- **The equation for the averages** `e = t M⁺ e + R` (`M⁺ = M^{(B)}∘M^{(B)}`; `lanlw`, `f = 1`). -/
theorem BAExp14a_e_eq (c : Zd d (sz.L n)) :
    BAExp14a_e sz z n t c = (t : ℂ) * ∑ b, (BAExp14a_MB sz z n c b) ^ 2 * BAExp14a_e sz z n t b + BAExp14a_R sz z n t c := by
  obtain ⟨-, -, hmi, -, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hx : ∀ x ∈ Iblk d (sz.L n) (sz.W n) c, ∫ ω, (baFMz sz z).GM n t ω x x ∂(BAExp14a_μ sz) =
      (t : ℂ) * ∑ b, (BAExp14a_MB sz z n c b) ^ 2 * BAExp14a_e sz z n t b +
        (t : ℂ) * ∑ α, (baFMz sz z).M n x α * BAExp14a_q sz z n t (STblk sz n α) α x := by
    intro x hx
    have hxc : (split d (sz.L n) (sz.W n) x).1 = c := by simpa [Iblk] using hx
    rw [BAExp14a_EGxx hκ hflow n ht0 ht hf x]
    simp only [Finset.sum_add_distrib]
    rw [BAExp14a_sumA hmi t (BAExp14a_e sz z n t) x, hxc]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring
  have he : BAExp14a_e sz z n t c = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, ∫ ω, (baFMz sz z).GM n t ω x x ∂(BAExp14a_μ sz) := by
    unfold BAExp14a_e BAExp14a_X
    simp only [integral_const_mul]
    rw [integral_finset_sum _ fun x _ => BAExp14a_int_GM hκ hflow n ht0 ht hf x x]
  rw [he, Finset.sum_congr rfl hx, Finset.sum_add_distrib, Finset.sum_const, card_Iblk, nsmul_eq_mul, mul_add, ← mul_assoc]
  unfold BAExp14a_R
  push_cast
  rw [inv_mul_cancel₀ hW, one_mul, ← Finset.mul_sum]
  ring

/-- **`‖e_c‖ ≤ CM ε₂/(1 - t)`** when `‖𝔼 [X_c Ǧ_{yw}]‖ ≤ ε₂` for all `c, y, w` (`‖R‖ ≤ CM ε₂`, the Neumann bound). -/
theorem BAExp14a_e_bound {ε₂ : ℝ} (hq : ∀ c y w, ‖BAExp14a_q sz z n t c y w‖ ≤ ε₂) (c : Zd d (sz.L n)) :
    ‖BAExp14a_e sz z n t c‖ ≤ CM * ε₂ / (1 - t) := by
  have hε₂ : 0 ≤ ε₂ := (norm_nonneg _).trans (hq 0 0 0)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  obtain ⟨-, hr, -, -, -⟩ := ba_G_data hκ sz hflow n ht0 ht
  refine BAExp14a_neumann (BAExp14a_MB sz z n) (BAExp14a_e sz z n t) (BAExp14a_R sz z n t) hf.ht0 hf.ht1
    (fun c => ?_) (fun c => BAExp14a_e_eq hκ hflow n ht0 ht hf c) (fun c => ?_) c
  · exact BAMB_row_sq_real d (sz.L n) _ _ _ hr.1 c
  · unfold BAExp14a_R
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, norm_mul, norm_inv, norm_pow,
      Complex.norm_natCast]
    have h1 : ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) c, ∑ α, (baFMz sz z).M n x α * BAExp14a_q sz z n t (STblk sz n α) α x‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ d * (CM * ε₂) := by
      calc _ ≤ ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, ∑ α, ‖(baFMz sz z).M n x α‖ * ε₂ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun α _ => ?_))
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hq _ _ _) (norm_nonneg _)
        _ ≤ ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, CM * ε₂ := by
            refine Finset.sum_le_sum fun x _ => ?_
            rw [← Finset.sum_mul]
            exact mul_le_mul_of_nonneg_right (hf.hMr x) hε₂
        _ = _ := by rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]; push_cast; ring
    calc t * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ x ∈ Iblk d (sz.L n) (sz.W n) c, ∑ α, (baFMz sz z).M n x α *
            BAExp14a_q sz z n t (STblk sz n α) α x‖)
        ≤ 1 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * (CM * ε₂))) :=
          mul_le_mul hf.ht1.le (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity) zero_le_one
      _ = CM * ε₂ := by field_simp

end ExpX3

section EnvBd

variable {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
  (hf : BAExp14a_Facts sz z n t CM S)
include hκ hflow ht0 ht hf

/-- **The polynomial envelope**: `‖F^Ǧ_k‖, ‖F^M_k‖ ≤ (36 K₃ + 6 S CM) N^{10}` for `N ≥ 1`, `η⁻¹ ≤ N²`. -/
theorem BAExp14a_env_bd {N : ℝ} (hN : 1 ≤ N) (hηN : ((baFMz sz z).eta n t)⁻¹ ≤ N ^ 2) (ω : sz.SeqΩ)
    (k : Fin 6) (σ : Bool) (a b : Zd d (sz.L n)) :
    ‖BAExp14a_FG sz z n t ω k σ a b‖ ≤ (36 * (5 / 2 * S * CM + CM * CM) + 6 * (S * CM)) * N ^ 10 ∧
      ‖BAExp14a_FM sz z n t ω k σ a b‖ ≤ (36 * (5 / 2 * S * CM + CM * CM) + 6 * (S * CM)) * N ^ 10 := by
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  have hK3 : 0 ≤ 5 / 2 * S * CM + CM * CM := by have := hf.hCM; positivity
  have hSC : 0 ≤ S * CM := mul_nonneg hS0 hf.hCM
  have hη := hf.hη
  have hA0 : ((baFMz sz z).eta n t)⁻¹ + 1 ≤ 2 * N ^ 2 := by nlinarith
  have ha : BAExp14a_a sz z n t ω ≤ ((baFMz sz z).eta n t)⁻¹ + 1 :=
    Finset.sup'_le _ _ fun c _ => BAExp14a_X_le hκ hflow n ht0 ht hf ω c
  have hb : BAExp14a_b sz z n t ω ≤ ((baFMz sz z).eta n t)⁻¹ + 1 :=
    Finset.sup'_le _ _ fun p _ => BAExp14a_GM_le hκ hflow n ht0 ht hf ω p.1 p.2
  have ha0 := BAExp14a_a_nonneg (sz := sz) (z := z) n t ω
  have hb0 := BAExp14a_b_nonneg (sz := sz) (z := z) n t ω
  have hWd0 : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hWd1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d :=
      one_le_pow₀ (by exact_mod_cast sz.W_pos n)
    exact inv_le_one_of_one_le₀ this
  have harith := BAExp14a_env_arith hN hη hηN hA0 ha0 hb0 ha hb hK3 hSC hWd0 hWd1
  have hJ0 := BAExp14a_Jm_nonneg hη hf.hCM hS0 ha0 hb0
  have hJ : BAExp14a_Jm ((baFMz sz z).eta n t) CM S (BAExp14a_a sz z n t ω) (BAExp14a_b sz z n t ω) =
      BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) * ((1 + BAExp14a_b sz z n t ω) /
        (baFMz sz z).eta n t))) := rfl
  have hJle : BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
      ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t))) ≤ (36 * (5 / 2 * S * CM + CM * CM) + 6 * (S * CM)) * N ^ 10 := by
    refine le_trans ?_ harith
    have : 0 ≤ BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
      ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t)))) := by positivity
    have h2 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (S * CM))) := by positivity
    have h3 : 0 ≤ BAExp14a_a sz z n t ω * (S * CM) := by positivity
    linarith
  by_cases hk : 2 ≤ k.val
  · refine ⟨?_, ?_⟩
    · refine (BAExp14a_FG_path_le hf k hk σ a b).trans ?_
      refine le_trans ?_ harith
      have h2 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (S * CM))) := by positivity
      have h3 : 0 ≤ BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
        ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t))) := by positivity
      have h4 : 0 ≤ BAExp14a_a sz z n t ω * (S * CM) := by positivity
      have : BAExp14a_b sz z n t ω * BAExp14a_Jm ((baFMz sz z).eta n t) CM S (BAExp14a_a sz z n t ω) (BAExp14a_b sz z n t ω) =
        BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
          ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t)))) := by rw [hJ]
      linarith
    · refine (BAExp14a_FM_path_le hf k hk σ a b).trans ?_
      refine le_trans ?_ hJle
      rw [hJ]
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
            ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t)))) ≤ 1 * (BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω *
            ((5 / 2 * S * CM + CM * CM) * ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t)))) :=
            mul_le_mul hWd1 le_rfl (by rw [← hJ]; exact hJ0) zero_le_one
        _ = _ := one_mul _
  · have hk' : k.val < 2 := by omega
    refine ⟨?_, ?_⟩
    · refine (BAExp14a_FG_lin_le hf k hk' σ a b).trans ?_
      refine le_trans ?_ harith
      have h3 : 0 ≤ BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
        ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t))) := by positivity
      have h4 : 0 ≤ BAExp14a_a sz z n t ω * (S * CM) := by positivity
      have h5 : 0 ≤ BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
        ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t)))) := by positivity
      linarith
    · refine (BAExp14a_FM_lin_le hf k hk' σ a b).trans ?_
      refine le_trans ?_ harith
      have h2 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (S * CM))) := by positivity
      have h3 : 0 ≤ BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
        ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t))) := by positivity
      have h5 : 0 ≤ BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (BAExp14a_a sz z n t ω * ((5 / 2 * S * CM + CM * CM) *
        ((1 + BAExp14a_b sz z n t ω) / (baFMz sz z).eta n t)))) := by positivity
      have h6 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BAExp14a_a sz z n t ω * (S * CM)) ≤ BAExp14a_a sz z n t ω * (S * CM) := by
        calc _ ≤ 1 * (BAExp14a_a sz z n t ω * (S * CM)) := mul_le_mul hWd1 le_rfl (by positivity) zero_le_one
          _ = _ := one_mul _
      linarith

end EnvBd

end Lanlw

/-! ## 9. `B ≤ 2`, `η⁻¹ ≤ N²`: the eventual scalar facts -/

section BctlTwo

/-- **`W^{-d} B_{u,0} ≤ 2`** once `λ² W^d ≥ 1` and `N (1 - u) ≥ 1` (a copy of `B45_STWB_le` at `K = 0`, `Induction/B45.lean:1259`,
private there; there is no BA analogue of `st5_Bctl_le_one`, `Induction/Step5Kit.lean:362`, which takes `STFlow`). -/
theorem BAExp14a_Bctl_le_two {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1)
    (hg : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hN : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u)) :
    sz.Bctl n u ≤ 2 := by
  have hv : 0 < 1 - u := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  have hg2 : 0 < sz.lam n ^ 2 := by
    by_contra h
    push Not at h
    have : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hW0.le
    linarith
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos hv]
  have hT1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := by
    have ha : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    exact ha
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
        ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by gcongr
    _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hNe]; field_simp
    _ ≤ 1 + 1 := by gcongr <;> exact inv_le_one_of_one_le₀ ‹_›
    _ = 2 := by norm_num

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- The eventual facts along the flow: `(1 - t)⁻¹ ≤ N`, `4 ≤ N`, `κ⁻¹ ≤ N`, `η⁻¹ ≤ N²`, `B ≤ 2`, `B ≥ 0`. -/
theorem BAExp14a_eventual_scalars (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧
      ((baFMz sz z).eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 ∧ sz.Bctl n (t n) ≤ 2 ∧ t n < 1 := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hWO := hflow.1.2.2.2.2
  filter_upwards [BAExp14a_eventually hκ hε hflow ht, hsz.eventually (eventually_ge_atTop (1 / κ)), hWO] with n hn hnk hwo
  obtain ⟨h1, h4, hg0, hgΛ⟩ := hn
  obtain ⟨ht1, hr, hmi, hzi, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht n)
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1t : 0 < 1 - t n := by linarith
  refine ⟨h1, h4, ?_, ?_, ht1⟩
  · -- η⁻¹ ≤ N²
    rw [BAExp14a_eta_eq]
    unfold etaOf
    rw [mul_inv]
    have hm : (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      refine le_trans (inv_anti₀ hκ hr.2) ?_
      have := hnk
      rwa [one_div] at this
    rw [sq]
    exact mul_le_mul h1 hm (inv_nonneg.2 hmi.le) hN0.le
  · refine BAExp14a_Bctl_le_two sz n ht1 ?_ ?_
    · have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have h2 := sz.lam_sq_mul_pow_ge n hwo.1
      refine le_trans ?_ h2
      exact Real.one_le_rpow hW1 (by linarith)
    · rw [inv_le_comm₀ h1t hN0] at h1
      rw [inv_eq_one_div, div_le_iff₀ hN0] at h1
      linarith

end BctlTwo

/-! ## 10. The pathwise bounds `P_g`, `P_m` and their `≺` -/

section PgPm

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (CM S : ℝ)

/-- The pathwise bound of `‖F^Ǧ_k‖` (all `k`): `b J_m + W^{-d} b a S CM`. -/
def BAExp14a_Pg (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  BAExp14a_b sz z n t ω * BAExp14a_Jm ((baFMz sz z).eta n t) CM S (BAExp14a_a sz z n t ω) (BAExp14a_b sz z n t ω) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (BAExp14a_b sz z n t ω * (BAExp14a_a sz z n t ω * (S * CM)))

/-- The pathwise bound of `‖F^M_k‖` for the four non-linear families: `W^{-d} J_m`. -/
def BAExp14a_Pm (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * BAExp14a_Jm ((baFMz sz z).eta n t) CM S (BAExp14a_a sz z n t ω) (BAExp14a_b sz z n t ω)

variable {sz z n CM S}

/-- **`P_g ≺ g_P`, `P_m ≺ g_M`** from `a ≺ B`, `b ≺ B^{1/2}`. -/
theorem BAExp14a_Dom_Pg_Pm {μ : Measure sz.SeqΩ} (hsz : Tendsto sz.size atTop atTop) {t : ℕ → ℝ} (hη : ∀ n, 0 < (baFMz sz z).eta n (t n))
    (hB : ∀ n, 0 ≤ sz.Bctl n (t n)) (hCM : 0 ≤ CM) (hS : 0 ≤ S)
    (hDa : BAExp14a_Dom sz μ (fun n ω => BAExp14a_a sz z n (t n) ω) (fun n => sz.Bctl n (t n)))
    (hDb : BAExp14a_Dom sz μ (fun n ω => BAExp14a_b sz z n (t n) ω) (fun n => (sz.Bctl n (t n)) ^ (1 / 2 : ℝ))) :
    BAExp14a_Dom sz μ (fun n ω => BAExp14a_Pg sz z n CM S (t n) ω)
        (fun n => (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * BAExp14a_gJ (5 / 2 * S * CM + CM * CM) (((baFMz sz z).eta n (t n))⁻¹) (sz.Bctl n (t n)) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (S * CM) * ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sz.Bctl n (t n))) ∧
      BAExp14a_Dom sz μ (fun n ω => BAExp14a_Pm sz z n CM S (t n) ω)
        (fun n => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * BAExp14a_gJ (5 / 2 * S * CM + CM * CM) (((baFMz sz z).eta n (t n))⁻¹) (sz.Bctl n (t n))) := by
  have hK3 : 0 ≤ 5 / 2 * S * CM + CM * CM := by positivity
  have hWd : ∀ n, 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := fun n => by positivity
  have hs : ∀ n, 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := fun n => Real.rpow_nonneg (hB n) _
  -- 1 + b ≺ 1 + B^{1/2}
  have d1 : BAExp14a_Dom sz μ (fun n ω => 1 + BAExp14a_b sz z n (t n) ω) (fun n => 1 + (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) :=
    BAExp14a_Dom.add hsz (BAExp14a_Dom.refl hsz (g := fun _ => (1 : ℝ)) fun _ => zero_le_one) hDb
  have d2 : BAExp14a_Dom sz μ (fun n ω => BAExp14a_a sz z n (t n) ω * BAExp14a_a sz z n (t n) ω)
      (fun n => sz.Bctl n (t n) * sz.Bctl n (t n)) :=
    BAExp14a_Dom.mul hsz (fun n ω => BAExp14a_a_nonneg n (t n) ω) hB hDa hDa
  have d3 : BAExp14a_Dom sz μ (fun n ω => BAExp14a_a sz z n (t n) ω * BAExp14a_a sz z n (t n) ω *
      (1 + BAExp14a_b sz z n (t n) ω)) (fun n => sz.Bctl n (t n) * sz.Bctl n (t n) * (1 + (sz.Bctl n (t n)) ^ (1 / 2 : ℝ))) :=
    BAExp14a_Dom.mul hsz (fun n ω => by have := BAExp14a_b_nonneg (sz := sz) (z := z) n (t n) ω; linarith)
      (fun n => mul_nonneg (hB n) (hB n)) d2 d1
  have d4 : BAExp14a_Dom sz μ (fun n ω => ((5 / 2 * S * CM + CM * CM) * ((baFMz sz z).eta n (t n))⁻¹) *
      (BAExp14a_a sz z n (t n) ω * BAExp14a_a sz z n (t n) ω * (1 + BAExp14a_b sz z n (t n) ω)))
      (fun n => BAExp14a_gJ (5 / 2 * S * CM + CM * CM) (((baFMz sz z).eta n (t n))⁻¹) (sz.Bctl n (t n))) :=
    BAExp14a_Dom.mul hsz (fun n ω => mul_nonneg (mul_nonneg (BAExp14a_a_nonneg n (t n) ω) (BAExp14a_a_nonneg n (t n) ω))
      (by have := BAExp14a_b_nonneg (sz := sz) (z := z) n (t n) ω; linarith))
      (fun n => mul_nonneg hK3 (inv_nonneg.2 (hη n).le))
      (BAExp14a_Dom.refl hsz (g := fun n => (5 / 2 * S * CM + CM * CM) * ((baFMz sz z).eta n (t n))⁻¹)
        fun n => mul_nonneg hK3 (inv_nonneg.2 (hη n).le)) d3
  have dJ : BAExp14a_Dom sz μ (fun n ω => BAExp14a_Jm ((baFMz sz z).eta n (t n)) CM S (BAExp14a_a sz z n (t n) ω)
      (BAExp14a_b sz z n (t n) ω)) (fun n => BAExp14a_gJ (5 / 2 * S * CM + CM * CM) (((baFMz sz z).eta n (t n))⁻¹) (sz.Bctl n (t n))) := by
    refine BAExp14a_Dom.of_le hsz (fun n ω => le_of_eq ?_) d4
    unfold BAExp14a_Jm
    rw [div_eq_mul_inv]
    ring
  have dba : BAExp14a_Dom sz μ (fun n ω => BAExp14a_b sz z n (t n) ω * BAExp14a_a sz z n (t n) ω)
      (fun n => (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sz.Bctl n (t n)) :=
    BAExp14a_Dom.mul hsz (fun n ω => BAExp14a_a_nonneg n (t n) ω) hs hDb hDa
  have hJ0 : ∀ n ω, 0 ≤ BAExp14a_Jm ((baFMz sz z).eta n (t n)) CM S (BAExp14a_a sz z n (t n) ω) (BAExp14a_b sz z n (t n) ω) :=
    fun n ω => BAExp14a_Jm_nonneg (hη n) hCM hS (BAExp14a_a_nonneg n (t n) ω) (BAExp14a_b_nonneg n (t n) ω)
  refine ⟨?_, ?_⟩
  · have e1 := BAExp14a_Dom.mul hsz hJ0 hs hDb dJ
    have e2 := BAExp14a_Dom.mul hsz (fun n ω => mul_nonneg (BAExp14a_b_nonneg (sz := sz) (z := z) n (t n) ω)
      (BAExp14a_a_nonneg n (t n) ω)) (fun n => mul_nonneg (hWd n) (mul_nonneg hS hCM))
      (BAExp14a_Dom.refl hsz (g := fun n => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (S * CM)) fun n => mul_nonneg (hWd n) (mul_nonneg hS hCM)) dba
    refine BAExp14a_Dom.of_le hsz (fun n ω => le_of_eq ?_) (BAExp14a_Dom.add hsz e1 e2)
    unfold BAExp14a_Pg
    ring
  · have e3 := BAExp14a_Dom.mul hsz hJ0 (fun n => hWd n)
      (BAExp14a_Dom.refl hsz (g := fun n => (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) hWd) dJ
    refine BAExp14a_Dom.of_le hsz (fun n ω => le_of_eq ?_) e3
    unfold BAExp14a_Pm
    rfl

end PgPm

/-! ## 11. The assembly of the `≺` statements -/

section Assembly

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- The eventual facts at `n`, in one conjunction. -/
theorem BAExp14a_ev (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hfacts : ∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S) (K0 : ℝ) :
    ∀ᶠ n in atTop, BAExp14a_Facts sz z n (t n) CM S ∧ (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧
      ((baFMz sz z).eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 ∧ sz.Bctl n (t n) ≤ 2 ∧ t n < 1 ∧ (0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹) ∧
      K0 ≤ ((sz.size n : ℕ) : ℝ) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  filter_upwards [hfacts, BAExp14a_eventual_scalars hκ hε h𝔡 hflow ht0 ht, hflow.1.2.2.2.2,
    hsz.eventually (eventually_ge_atTop K0)] with n hF hS hWO hK0
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  exact ⟨hF (t n) (ht0 n) (ht n), hS.1, hS.2.1, hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2,
    ⟨(Real.rpow_nonneg hW0 _).trans hWO.1, hWO.2⟩, hK0⟩

/-- `t < 1` along the flow. -/
theorem BAExp14a_t_lt_one (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht : ∀ n, t n ≤ BAflowT0 sz z n) (n : ℕ) :
    t n < 1 := lt_of_le_of_lt (ht n) (BAflow_T0_bounds hκ hflow n).2.2.2

/-- `η⁻¹ ≤ κ⁻¹ (1 - t)⁻¹` (`Im m ≥ κ`). -/
theorem BAExp14a_eta_inv_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht1 : t < 1) :
    ((baFMz sz z).eta n t)⁻¹ ≤ κ⁻¹ * (1 - t)⁻¹ := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  rw [BAExp14a_eta_eq]
  unfold etaOf
  rw [mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hκ hr.2) (inv_nonneg.2 (by linarith))

/-- The floor `N^{-5/2} ≤ (1 - t)⁻¹ B^{5/2}`. -/
theorem BAExp14a_floor (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((sz.size n : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (1 - t)⁻¹ * (sz.Bctl n t) ^ (5 / 2 : ℝ) := by
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 := Sizes.expAvg_Bctl_ge sz n ht0 ht1
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) ≤ (sz.Bctl n t) ^ (5 / 2 : ℝ) := by
    rw [Real.rpow_neg hN.le, ← Real.inv_rpow hN.le]
    exact Real.rpow_le_rpow (inv_nonneg.2 hN.le) h1 (by norm_num)
  have h3 : 1 ≤ (1 - t)⁻¹ := by
    rw [one_le_inv₀ (by linarith)]; linarith
  have h4 : 0 ≤ (sz.Bctl n t) ^ (5 / 2 : ℝ) := Real.rpow_nonneg (STBctl_pos sz n ht1).le _
  nlinarith

/-- **`𝔼 F^Ǧ ≺ (1 - t)⁻¹ B^{5/2}`**, uniformly in `(k, σ, a, b)`: the pathwise bound `‖F^Ǧ‖ ≤ P_g ≺ g_P ≤ K ζ`, then `≺ → 𝔼`. -/
theorem BAExp14a_FG_prec (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) {CM S : ℝ} (hCM : 0 ≤ CM) (hS : 1 ≤ S)
    (hfacts : ∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S)
    (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t) (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Fin 6 × Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14a_FG sz z n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hη : ∀ n, 0 < (baFMz sz z).eta n (t n) := fun n => BAExp14a_eta_pos hκ hflow n (ht0 n) (ht n)
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hS0 : 0 ≤ S := by linarith
  have hDa := BAExp14a_Dom_a (μ := BAExp14a_μ sz) t hflow hκ hA
  have hDb := BAExp14a_Dom_b (μ := BAExp14a_μ sz) (κ := κ) (ε := ε) (𝔠 := 𝔠) (𝔡 := 𝔡) t ht1 hE
  obtain ⟨hPg, -⟩ := BAExp14a_Dom_Pg_Pm hsz hη hB hCM hS0 hDa hDb
  have hK3 : 0 ≤ 5 / 2 * S * CM + CM * CM := by positivity
  set c1 : ℝ := (𝔡⁻¹) ^ 2 + 1 with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hSC : 0 ≤ S * CM := mul_nonneg hS0 hCM
  set K : ℝ := 3 * (5 / 2 * S * CM + CM * CM) * κ⁻¹ + c1 * (S * CM) + 1 with hK
  have hKpos : 0 < K := by
    have : 0 ≤ 3 * (5 / 2 * S * CM + CM * CM) * κ⁻¹ := by positivity
    have : 0 ≤ c1 * (S * CM) := by positivity
    linarith
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts (72 * (5 / 2 * S * CM + CM * CM) + 12 * (S * CM))
  refine BAExp14a_prec_int (μ := BAExp14a_μ sz) hsz (V := fun n => Fin 6 × Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (fun n p ω => BAExp14a_FG sz z n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun n ω => BAExp14a_Pg sz z n CM S (t n) ω) _ (fun n => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) (K := K)
    (Kenv := 11) (Kf := 5 / 2) hKpos (fun n => ?_) ?_ hPg ?_ ?_ ?_
  · exact mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (Real.rpow_nonneg (hB n) _)
  · filter_upwards [hev] with n hn p ω
    obtain ⟨hf, -⟩ := hn
    obtain ⟨k0, σ, a, b⟩ := p
    by_cases hk : 2 ≤ k0.val
    · refine (BAExp14a_FG_path_le (ω := ω) hf k0 hk σ a b).trans ?_
      unfold BAExp14a_Pg
      have : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * (BAExp14a_b sz z n (t n) ω * (BAExp14a_a sz z n (t n) ω * (S * CM))) := by
        have := BAExp14a_a_nonneg (sz := sz) (z := z) n (t n) ω
        have := BAExp14a_b_nonneg (sz := sz) (z := z) n (t n) ω
        positivity
      linarith
    · have := BAExp14a_FG_lin_le (ω := ω) hf k0 (by omega) σ a b
      refine this.trans ?_
      unfold BAExp14a_Pg
      have h0 : 0 ≤ BAExp14a_b sz z n (t n) ω * BAExp14a_Jm ((baFMz sz z).eta n (t n)) CM S (BAExp14a_a sz z n (t n) ω)
          (BAExp14a_b sz z n (t n) ω) :=
        mul_nonneg (BAExp14a_b_nonneg n (t n) ω) (BAExp14a_Jm_nonneg hf.hη hf.hCM hS0 (BAExp14a_a_nonneg n (t n) ω)
          (BAExp14a_b_nonneg n (t n) ω))
      linarith
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    have hBpos := STBctl_pos sz n ht1n
    have hWd := BAExp14a_Wd_le (sz := sz) n (ht0 n) ht1n
    have hWdc : (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ ≤ c1 * sz.Bctl n (t n) := by
      refine hWd.trans (mul_le_mul_of_nonneg_right ?_ hBpos.le)
      rw [hc1]
      have : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
      linarith
    have hηi := BAExp14a_eta_inv_le hκ hflow n ht1n
    have hη0 : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := inv_nonneg.2 (hη n).le
    have h1t' : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    obtain ⟨c1', -⟩ := BAExp14a_cmp (B := sz.Bctl n (t n)) (Wd := (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) (c1 := c1) (K3 := 5 / 2 * S * CM + CM * CM)
      (SC := S * CM) (ηi := ((baFMz sz z).eta n (t n))⁻¹) (κi := κ⁻¹) (ω1 := (1 - t n)⁻¹) hBpos hB2 hK3 hSC hWdc
      (by positivity) hc10 hηi hη0 (inv_nonneg.2 hκ.le) h1t'
    refine c1'.trans ?_
    have hz : 0 ≤ (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) :=
      mul_nonneg (inv_nonneg.2 (by linarith)) (Real.rpow_nonneg hBpos.le _)
    rw [hK]
    nlinarith
  · filter_upwards [hev] with n hn p ω
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨k0, σ, a, b⟩ := p
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
    have h := (BAExp14a_env_bd hκ hflow n (ht0 n) (ht n) hf hN1 hηN ω k0 σ a b).1
    calc ‖BAExp14a_FG sz z n (t n) ω k0 σ a b‖ ≤ (36 * (5 / 2 * S * CM + CM * CM) + 6 * (S * CM)) * ((sz.size n : ℕ) : ℝ) ^ 10 := h
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 10 := by
          have hpos : 0 ≤ 36 * (5 / 2 * S * CM + CM * CM) + 6 * (S * CM) := by positivity
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = ((sz.size n : ℕ) : ℝ) ^ (11 : ℝ) := by
          rw [show (11 : ℝ) = ((11 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  · filter_upwards [hev] with n hn
    exact BAExp14a_floor n (ht0 n) hn.2.2.2.2.2.1

end Assembly

end RBM.BA

end
