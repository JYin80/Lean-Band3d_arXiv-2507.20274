/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14aB
import RBM3D.BA.TwistPins

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false

/-!
# BA-L L4b1 (T2434), part A: the pins S2, S3 of `lem:LWterm_EXP` at BA, their integrands, and the deterministic block algebra

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:7-121` (`(eq:ELW_term)`), `GGGamma` `:393-405` (D402: the first two sums carry
`W - 1 = M⁺S⁺`), `lanlw` `:359-372`; design `docs/reports/T2398-design.md` §1, §2; family table and statements `docs/reports/T2434-prove.md`
(i), (iv); consumer `BALWCutExpTw` (`t/T2398:RBM3D/Probe/T2398Pins.lean:434-440`); S1 is `BAExp14aS1` (`Graph/BAExp14aB.lean:124`, merged).
Section 1 is the probe `RBM3D/Probe/T2434Pins.lean` of this ticket (never merged), copied verbatim.  Part B is `Graph/BAExp14bB.lean`.

The sum behind the cut at the carrier `baFMz` (`C.S = 1`) is, for `σc = true`,
`LWcutg = W^{-2d} Σ_{x ∈ [ao], y ∈ [ac], α} X_{[α]} G_{xα} G_{αy} G(σo)_{yx}` (`BAExp14a_L1_eq`).  Write `f = X_{[α]} G(σo)_{yx}`, `G = Ǧ + M`:
`ǦǦ` is `BAGGGammaR` at `(x, y, y') := (α, y, x)`: `T1`, `T2a`, `T2b`, `T3A_k`, `T3B_k`, `T3C_k`, `k ∈ {0, 1}`, `W^{(0)} = 1`, `W^{(1)} = W - 1`;
`MǦ` is `BAlanlwR` at `(α, y)`, `ǦM` is `BAlanlwR` at `(x, α)`: `C1`, `C2` (children `Ǧ_{ββ}`) and `D1`, `D2` (children `∂f`); `MM` has no expansion.
`∂f = (∂X) G(σo)_{yx} + X ∂G(σo)_{yx}` splits `D1`, `D2`, `T3C` into a `∂X` part (S3) and a `∂tail` part (S2).
`S1 = {MM, T1, T3A_0, T3A_1, C1, C2}` (merged).  `S2 = {D1t, D2t, T2a, T2b, T3B_0, T3B_1, T3C-Ḡ_0, T3C-Ḡ_1}`, `S3 = {D1X, D2X, T3C-tr_0, T3C-tr_1}`.

S2 is proved by row L4b2, S3 by the rows L4g/L4c1/L4d2 (Amend 1 item 3: the roots of the S3 families have `M`-dotted edges); this row proves neither.
-/

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

section S2S3Fam
variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- `∂_{h_{δγ}}` of the closing edge `G(σ)_{yx}`: `-G_{yδ} G_{γx}` for `σ = true`, `-\overline{G_{xγ} G_{δy}}` for `σ = false`
(`BAExpand_dh_of_partial`, `BAExpand_dh_star_of_partial`, `Graph/BAExpand.lean:193, 217`). -/
def BAExp14b_dtail (σ : Bool) (x y δ γ : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if σ then -((baFMz sz z).G n t ω y δ * (baFMz sz z).G n t ω γ x)
  else -star ((baFMz sz z).G n t ω x γ * (baFMz sz z).G n t ω δ y)

/-- `∂_{h_{δγ}} X_{[α]} = -W^{-d} Σ_{v ∈ [α]} G_{vδ} G_{γv}` (`X_c = W^{-d} Σ_{v ∈ [c]} Ǧ_{vv}`, `M` constant). -/
def BAExp14b_dX (α δ γ : Idx d (sz.L n) (sz.W n)) : ℂ :=
  -((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ v ∈ Iblk d (sz.L n) (sz.W n) (STblk sz n α),
    (baFMz sz z).G n t ω v δ * (baFMz sz z).G n t ω γ v)

/-- `W^{-2d} Σ_{x ∈ [a], y ∈ [b]} Σ_α X_{[α]} T(x, y, α)`: the frame of `BAExp14a_outer` without the closing edge, which is differentiated
(`∂tail` sits inside `T`). -/
def BAExp14b_outerDt (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
    ∑ α, BAExp14a_X sz z n t ω (STblk sz n α) * T x y α

/-- `W^{-2d} Σ_{x ∈ [a], y ∈ [b]} G(σ)_{yx} Σ_α T(x, y, α)`: the frame of `BAExp14a_outer` without `X_{[α]}`, which is differentiated
(`∂X` sits inside `T`). -/
def BAExp14b_outerDX (σ : Bool) (a b : Zd d (sz.L n))
    (T : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b,
    BAExp14a_tail sz z n t ω σ x y * ∑ α, T x y α

/-! ### S2: the eight twisted families (`x ∈ [a]`, `y ∈ [b]`, closing edge `G(σ)_{yx}`, loop charge `+`) -/

/-- `D1t`: `-Σ_{α', β} M_{xα} M_{αα'} S_{α'β} G_{βy} X_{[α]} ∂_{h_{βα'}} G(σ)_{yx}` (`lanlw` on `M_{xα} Ǧ_{αy}`, the `∂tail` child). -/
def BAExp14b_FD1t (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14b_outerDt sz z n t ω a b fun x y α => ∑ α', ∑ β,
    -((baFMz sz z).M n x α * (baFMz sz z).M n α α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β y *
      BAExp14b_dtail sz z n t ω σ x y β α')

/-- `D2t`: `-Σ_{α', β} M_{xα'} S_{α'β} G_{βα} M_{αy} X_{[α]} ∂_{h_{βα'}} G(σ)_{yx}` (`lanlw` on `Ǧ_{xα} M_{αy}`, the `∂tail` child). -/
def BAExp14b_FD2t (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14b_outerDt sz z n t ω a b fun x y α => ∑ α', ∑ β,
    -((baFMz sz z).M n x α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β α * (baFMz sz z).M n α y *
      BAExp14b_dtail sz z n t ω σ x y β α')

/-- `T2a`: `Σ_β (W - 1)_{αβ} Ǧ_{βy} M_{xβ}` (second sum of `GGGamma`, D402). -/
def BAExp14b_FT2a (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).GM n t ω β y * (baFMz sz z).M n x β

/-- `T2b`: `Σ_β (W - 1)_{αβ} M_{βy} Ǧ_{xβ}`. -/
def BAExp14b_FT2b (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α =>
    ∑ β, BAExp14a_Wk sz z n t true α β * (baFMz sz z).M n β y * (baFMz sz z).GM n t ω x β

/-- `T3B^{(k)}`: `Σ_{w, γ, δ} W^{(k)}_{αw} M_{wγ} S_{γδ} Ǧ_{γw} G_{δy} G_{xδ}` (the `Ǧ_{γw} G_{δy} G_{xδ}` term of `GGGamma`). -/
def BAExp14b_FT3B (k : Bool) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14a_outer sz z n t ω σ a b fun x y α => ∑ w, ∑ γ, ∑ δ,
    BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).GM n t ω γ w *
      (baFMz sz z).G n t ω δ y * (baFMz sz z).G n t ω x δ

/-- `T3C-Ḡ^{(k)}`: `-Σ_{w, γ, δ} W^{(k)}_{αw} M_{wγ} S_{γδ} G_{δy} Ǧ_{xw} X_{[α]} ∂_{h_{δγ}} G(σ)_{yx}` (the `∂f` term of `GGGamma`, tail part). -/
def BAExp14b_FT3CG (k : Bool) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14b_outerDt sz z n t ω a b fun x y α => ∑ w, ∑ γ, ∑ δ,
    -(BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).G n t ω δ y *
      (baFMz sz z).GM n t ω x w * BAExp14b_dtail sz z n t ω σ x y δ γ)

/-- The eight families of S2 at the loop charge `+`, in the order `D1t, D2t, T2a, T2b, T3B^{(0)}, T3B^{(1)}, T3C-Ḡ^{(0)}, T3C-Ḡ^{(1)}`. -/
def BAExp14b_FS2 (j : Fin 8) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ![BAExp14b_FD1t sz z n t ω σ a b, BAExp14b_FD2t sz z n t ω σ a b, BAExp14b_FT2a sz z n t ω σ a b, BAExp14b_FT2b sz z n t ω σ a b,
    BAExp14b_FT3B sz z n t ω false σ a b, BAExp14b_FT3B sz z n t ω true σ a b, BAExp14b_FT3CG sz z n t ω false σ a b,
    BAExp14b_FT3CG sz z n t ω true σ a b] j

/-! ### S3: the four graph families (the `∂X_{[α]}` parts) -/

/-- `D1X`: `-Σ_{α', β} M_{xα} M_{αα'} S_{α'β} G_{βy} (∂_{h_{βα'}} X_{[α]}) G(σ)_{yx}` (`lanlw` on `M_{xα} Ǧ_{αy}`, the `∂X` child). -/
def BAExp14b_FD1X (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14b_outerDX sz z n t ω σ a b fun x y α => ∑ α', ∑ β,
    -((baFMz sz z).M n x α * (baFMz sz z).M n α α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β y *
      BAExp14b_dX sz z n t ω α β α')

/-- `D2X`: `-Σ_{α', β} M_{xα'} S_{α'β} G_{βα} M_{αy} (∂_{h_{βα'}} X_{[α]}) G(σ)_{yx}` (`lanlw` on `Ǧ_{xα} M_{αy}`, the `∂X` child). -/
def BAExp14b_FD2X (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14b_outerDX sz z n t ω σ a b fun x y α => ∑ α', ∑ β,
    -((baFMz sz z).M n x α' * BAlwS d (sz.L n) (sz.W n) t α' β * (baFMz sz z).G n t ω β α * (baFMz sz z).M n α y *
      BAExp14b_dX sz z n t ω α β α')

/-- `T3C-tr^{(k)}`: `-Σ_{w, γ, δ} W^{(k)}_{αw} M_{wγ} S_{γδ} G_{δy} Ǧ_{xw} (∂_{h_{δγ}} X_{[α]}) G(σ)_{yx}` (the `∂f` term of `GGGamma`, loop part). -/
def BAExp14b_FT3CX (k : Bool) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  BAExp14b_outerDX sz z n t ω σ a b fun x y α => ∑ w, ∑ γ, ∑ δ,
    -(BAExp14a_Wk sz z n t k α w * (baFMz sz z).M n w γ * BAlwS d (sz.L n) (sz.W n) t γ δ * (baFMz sz z).G n t ω δ y *
      (baFMz sz z).GM n t ω x w * BAExp14b_dX sz z n t ω α δ γ)

/-- The four families of S3 at the loop charge `+`, in the order `D1X, D2X, T3C-tr^{(0)}, T3C-tr^{(1)}`. -/
def BAExp14b_FS3 (j : Fin 4) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ![BAExp14b_FD1X sz z n t ω σ a b, BAExp14b_FD2X sz z n t ω σ a b, BAExp14b_FT3CX sz z n t ω false σ a b,
    BAExp14b_FT3CX sz z n t ω true σ a b] j

/-- **The integrand of S2** at the labelling of `LWcutg`, the `σc` convention of `BAExp14aS1Fam`: for `σc = true` the family `j` over
`x ∈ [ao]`, `y ∈ [ac]`, closing edge `G(σo)_{yx}`; for `σc = false` the complex conjugate of the blue family at the swapped blocks and the
flipped tail charge (the conjugation `BAExp14bCutConj`). -/
def BAExp14bS2Fam (j : Fin 8) (σc σo : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  if σc then BAExp14b_FS2 sz z n t ω j σo ao ac else star (BAExp14b_FS2 sz z n t ω j (!σo) ac ao)

/-- **The integrand of S3** (as `BAExp14bS2Fam`). -/
def BAExp14bS3Fam (j : Fin 4) (σc σo : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  if σc then BAExp14b_FS3 sz z n t ω j σo ao ac else star (BAExp14b_FS3 sz z n t ω j (!σo) ac ao)

end S2S3Fam

/-- **S2** (the twisted families of `lem:LWterm_EXP` at BA; owner row L4b2): for the eight families `D1t, D2t, T2a, T2b, T3B^{(k)}, T3C-Ḡ^{(k)}`
(`BAExp14bS2Fam`), every charge pair and every block pair, `‖𝔼 F‖ ≺ (1 - t)⁻¹ (W^{-d} B_{t,0})^{5/2}` on `U_n = {λ²/L^d ≤ 1 - t}`, over the carrier
`baFMz sz z` and the law `seqP (sz.withLam 0)`, from the seven premises of `BALWCutExpTw` (the five Step 1/2 pins, `BATwistAvgLaw` (TL1),
`BATwistLoopLaw` (TL2)).  Binders, range of `t`, `U` and bound as `BAExp14aS1`. -/
def BAExp14bS2 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : Fin 8 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, BAExp14bS2Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **S3** (the graph families, the `∂X` parts; owner rows L4g, L4c1): for the four families `D1X, D2X, T3C-tr^{(k)}` (`BAExp14bS3Fam`), the same
bound, from the five premises of `LWCutExpG` (the Step 1/2 pins; no `BATwist*`).  The roots of these families are not `baG5Graph` (`mdot ≠ []`,
`docs/reports/T2434-prove.md` (iii)): their identity, closure and leaf bound are owed to a successor row (Amend 1 item 3). -/
def BAExp14bS3 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => {_p : Fin 4 × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, BAExp14bS3Fam sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂μ‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- **The expansion identity** (target 2 of the row; no premise on the law beyond `BAFlow`): the cut in expectation is the sum of the six S1
families (`BAExp14aS1Fam`), the eight S2 families and the four S3 families, at every size `n`, time `t ∈ [0, BAflowT0]` and labelling
`(σc, σo, ac, ao)`, both charges (the red charge through `BAExp14bCutConj`).  Quantified as `baExp14a_S1_holds`. -/
def BAExp14bExpand (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (σc σo : Bool) (ac ao : Zd d (sz.L n)),
      ∫ ω, LWcutg (baFMz sz z) n t σc σo ac ao ω ∂(Sizes.seqP (sz.withLam 0)) =
        (∑ k : Fin 6, ∫ ω, BAExp14aS1Fam sz z n t ω k σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))) +
        (∑ j : Fin 8, ∫ ω, BAExp14bS2Fam sz z n t ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))) +
        (∑ j : Fin 4, ∫ ω, BAExp14bS3Fam sz z n t ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0)))

/-- **The conjugation** the identity uses for `σc = false`, pathwise (`Gres false = G^*`, `Eblk` real, `C.S = 1`, `star (C.m)`; band
`lwExpTerm2_cut_conj`; `docs/reports/T2418-prove.md` (d) O4). -/
def BAExp14bCutConj {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : ℝ) (σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ),
    LWcutg (baFMz sz z) n t false σo ac ao ω = star (LWcutg (baFMz sz z) n t true (!σo) ao ac ω)

/-! ## 2. The loops of the carrier as fine sums (`𝓛^{(k)} = tr Π G(σ_i) E_{a_i}`) -/

section Loop3

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem BAExp14b_gres_blockMat (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ : Bool) :
    Gres (blockMat d L W H) z σ = Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) (Gres H z σ) := by
  unfold Gres blockMat
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix
        (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    ext i j
    cases σ <;> simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  simp

/-- The block weight `(E_a)_{xx} = W^{-d} 1[x ∈ [a]]` on the fine lattice. -/
private def BAExp14b_dw (a : Zd d L) (x : Idx d L W) : ℂ := if (split d L W x).1 = a then ((W : ℂ) ^ d)⁻¹ else 0

private theorem BAExp14b_Eblk_reindex (a : Zd d L) :
    Eblk d L W a = Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) (Matrix.diagonal (BAExp14b_dw a)) := by
  ext p q
  have h : split d L W ((splitEquiv d L W).symm p) = p := (splitEquiv d L W).apply_symm_apply p
  simp [Eblk, BAExp14b_dw, Matrix.diagonal_apply, h]

private theorem BAExp14b_trace_reindex (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  exact Equiv.sum_comp (splitEquiv d L W).symm (fun i => M i i) |>.symm ▸ rfl

private theorem BAExp14b_loop_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d L) :
    loopFine d L W H z σ a = Matrix.trace (List.ofFn fun i =>
      Gres H z (σ i) * Matrix.diagonal (BAExp14b_dw (a i))).prod := by
  unfold loopFine loopM
  simp only [BAExp14b_gres_blockMat, BAExp14b_Eblk_reindex, ← map_mul]
  have h : (List.ofFn fun i => Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W)
      (Gres H z (σ i) * Matrix.diagonal (BAExp14b_dw (a i)))) =
      (List.ofFn fun i => Gres H z (σ i) * Matrix.diagonal (BAExp14b_dw (a i))).map
        (Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W)) := List.map_ofFn.symm
  rw [h, ← map_list_prod, BAExp14b_trace_reindex]

private theorem BAExp14b_trace_prod3 {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Fin 3 → Matrix ι ι ℂ) :
    Matrix.trace (List.ofFn P).prod = ∑ x, ∑ y, ∑ z, P 0 x y * (P 1 y z * P 2 z x) := by
  simp [List.ofFn_succ, Matrix.trace, Matrix.mul_apply, Finset.mul_sum]

/-- **`𝓛^{(3)}` as a triple fine sum**: `tr(G(σ₁)E_a G(σ₂)E_b G(σ₃)E_c) = W^{-3d} Σ_{x ∈ [c]} Σ_{α ∈ [a]} Σ_{y ∈ [b]} G(σ₁)_{xα} G(σ₂)_{αy} G(σ₃)_{yx}`. -/
theorem BAExp14b_loop3 (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ₁ σ₂ σ₃ : Bool) (a b c : Zd d L) :
    loopFine d L W H z ![σ₁, σ₂, σ₃] ![a, b, c] =
      (((W : ℂ) ^ d)⁻¹) ^ 3 * ∑ x ∈ Iblk d L W c, ∑ α ∈ Iblk d L W a, ∑ y ∈ Iblk d L W b,
        Gres H z σ₁ x α * Gres H z σ₂ α y * Gres H z σ₃ y x := by
  rw [BAExp14b_loop_eq, BAExp14b_trace_prod3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.mul_diagonal, BAExp14b_dw]
  have e : ∀ x x1 x2 : Idx d L W,
      (Gres H z σ₁ x x1 * if (split d L W x1).1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        ((Gres H z σ₂ x1 x2 * if (split d L W x2).1 = b then ((W : ℂ) ^ d)⁻¹ else 0) *
          (Gres H z σ₃ x2 x * if (split d L W x).1 = c then ((W : ℂ) ^ d)⁻¹ else 0)) =
      if (split d L W x).1 = c then (if (split d L W x1).1 = a then (if (split d L W x2).1 = b then
        (((W : ℂ) ^ d)⁻¹) ^ 3 * (Gres H z σ₁ x x1 * Gres H z σ₂ x1 x2 * Gres H z σ₃ x2 x) else 0) else 0) else 0 := by
    intro x x1 x2
    by_cases h1 : (split d L W x1).1 = a <;> by_cases h2 : (split d L W x2).1 = b <;>
      by_cases h3 : (split d L W x).1 = c <;> simp [h1, h2, h3] <;> ring
  simp only [e]
  simp only [Iblk, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (split d L W x).1 = c
  · simp only [hx, ite_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    by_cases h1 : (split d L W x1).1 = a
    · simp only [h1, ite_true]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x2 _ => ?_
      by_cases h2 : (split d L W x2).1 = b
      · simp [h2]
      · simp [h2]
    · simp [h1]
  · simp [hx]

private theorem BAExp14b_trace_prod1 {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Fin 1 → Matrix ι ι ℂ) :
    Matrix.trace (List.ofFn P).prod = ∑ x, P 0 x x := by
  simp [List.ofFn_succ, Matrix.trace]

/-- **`𝓛^{(1)}` as a fine sum**: `tr(G(σ) E_c) = W^{-d} Σ_{x ∈ [c]} G(σ)_{xx}`. -/
theorem BAExp14b_loop1 (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ : Bool) (c : Zd d L) :
    loopFine d L W H z ![σ] ![c] = (((W : ℂ) ^ d))⁻¹ * ∑ x ∈ Iblk d L W c, Gres H z σ x x := by
  rw [BAExp14b_loop_eq, BAExp14b_trace_prod1]
  simp only [Matrix.cons_val_zero, Matrix.mul_diagonal, BAExp14b_dw]
  simp only [Iblk, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : (split d L W x).1 = c <;> simp [h, mul_comm]

/-- `\overline{G(σ)_{ab}} = G(!σ)_{ba}` for Hermitian `H`. -/
theorem BAExp14b_star_Gres {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (a b : Idx d L W) :
    star (Gres H z σ a b) = Gres H z (!σ) b a := by
  cases σ
  · simp only [Bool.not_false]
    rw [lwWx_Gres_false hH z a b, star_star]
  · simp only [Bool.not_true]
    rw [lwWx_Gres_false hH z b a]

private theorem BAExp14b_star_winv : star (((W : ℂ) ^ d)⁻¹) = ((W : ℂ) ^ d)⁻¹ := by
  rw [star_inv₀, star_pow]; simp

theorem BAExp14b_loop1_conj {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (c : Zd d L) :
    star (loopFine d L W H z ![σ] ![c]) = loopFine d L W H z ![!σ] ![c] := by
  rw [BAExp14b_loop1, BAExp14b_loop1, star_mul', star_sum, BAExp14b_star_winv]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [BAExp14b_star_Gres hH]

private theorem BAExp14b_sum3_rev {γ : Type*} [AddCommMonoid γ] {ι₁ ι₂ ι₃ : Type*} (s : Finset ι₁) (t : Finset ι₂) (u : Finset ι₃)
    (f : ι₁ → ι₂ → ι₃ → γ) : ∑ x ∈ s, ∑ α ∈ t, ∑ y ∈ u, f x α y = ∑ y ∈ u, ∑ α ∈ t, ∑ x ∈ s, f x α y := by
  calc ∑ x ∈ s, ∑ α ∈ t, ∑ y ∈ u, f x α y = ∑ x ∈ s, ∑ y ∈ u, ∑ α ∈ t, f x α y :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ y ∈ u, ∑ x ∈ s, ∑ α ∈ t, f x α y := Finset.sum_comm
    _ = ∑ y ∈ u, ∑ α ∈ t, ∑ x ∈ s, f x α y := Finset.sum_congr rfl fun y _ => Finset.sum_comm

theorem BAExp14b_loop3_conj {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (a b c : Zd d L) :
    star (loopFine d L W H z ![true, true, σ] ![a, b, c]) = loopFine d L W H z ![false, false, !σ] ![a, c, b] := by
  rw [BAExp14b_loop3, BAExp14b_loop3, star_mul', star_pow, BAExp14b_star_winv]
  congr 1
  rw [star_sum]
  simp only [star_sum, star_mul', BAExp14b_star_Gres hH]
  rw [BAExp14b_sum3_rev]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [Bool.not_true]
  ring

end Loop3

section Fibre

theorem BAExp14b_vec1 {γ : Type*} (b : γ) : (![b] : Fin 1 → γ) = fun _ => b := by
  funext i; fin_cases i; rfl

/-- `Σ_{a} Σ_{α ∈ [a]} h(a, α) = Σ_α h([α], α)`. -/
theorem BAExp14b_sum_fibre {d L W : ℕ} [NeZero L] [NeZero W] (h : Zd d L → Idx d L W → ℂ) :
    ∑ a : Zd d L, ∑ α ∈ Iblk d L W a, h a α = ∑ α : Idx d L W, h (split d L W α).1 α := by
  rw [← Finset.sum_fiberwise Finset.univ (fun α : Idx d L W => (split d L W α).1) (fun α => h (split d L W α).1 α)]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr ?_ fun α hα => ?_
  · ext α; simp [Iblk]
  · have : (split d L W α).1 = a := by simpa [Iblk] using hα
    rw [this]


end Fibre

end RBM.BA

end
