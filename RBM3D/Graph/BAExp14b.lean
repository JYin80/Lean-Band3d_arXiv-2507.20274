/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14aB
import RBM3D.BA.TwistPins

/-!
# BA-L L4b1 (T2434), part A: the pins S2, S3 of `lem:LWterm_EXP`, the block algebra

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:7-121` (`(eq:ELW_term)`), `GGGamma`
`:393-405` (D402: the first two sums carry `W - 1 = M⁺S⁺`), `lanlw` `:359-372`; design
`docs/reports/T2398-design.md` §1, §2; family table and statements `docs/reports/T2434-prove.md`
(i), (iv); consumer `BALWCutExpTw` (`t/T2398:RBM3D/Probe/T2398Pins.lean:434-440`); S1 is
`BAExp14aS1` (`Graph/BAExp14aB.lean:124`, merged). Section 1 is the probe
`RBM3D/Probe/T2434Pins.lean` of this ticket (never merged), copied verbatim.  Part B is
`Graph/BAExp14bB.lean`.

The sum behind the cut at the carrier `baFMz` (`C.S = 1`) is, for `σc = true`,
`LWcutg = W^{-2d} Σ_{x ∈ [ao], y ∈ [ac], α} X_{[α]} G_{xα} G_{αy} G(σo)_{yx}` (`BAExp14a_L1_eq`).
Write `f = X_{[α]} G(σo)_{yx}`, `G = Ǧ + M`: `ǦǦ` is `BAGGGammaR` at `(x, y, y') := (α, y, x)`:
`T1`, `T2a`, `T2b`, `T3A_k`, `T3B_k`, `T3C_k`, `k ∈ {0, 1}`, `W^{(0)} = 1`, `W^{(1)} = W - 1`; `MǦ`
is `BAlanlwR` at `(α, y)`, `ǦM` is `BAlanlwR` at `(x, α)`: `C1`, `C2` (children `Ǧ_{ββ}`) and `D1`,
`D2` (children `∂f`); `MM` has no expansion. `∂f = (∂X) G(σo)_{yx} + X ∂G(σo)_{yx}` splits `D1`,
`D2`, `T3C` into a `∂X` part (S3) and a `∂tail` part (S2). `S1 = {MM, T1, T3A_0, T3A_1, C1, C2}`
(merged).  `S2 = {D1t, D2t, T2a, T2b, T3B_0, T3B_1, T3C-Ḡ_0, T3C-Ḡ_1}`,
`S3 = {D1X, D2X, T3C-tr_0, T3C-tr_1}`.

S2 is proved by row L4b2, S3 by the rows L4g/L4c1/L4d2 (Amend 1 item 3: the roots of the S3 families
have `M`-dotted edges); this row proves neither.

Contents.  §1 the pins `BAExp14bS2`, `BAExp14bS3`, `BAExp14bExpand`, `BAExp14bCutConj` and the
fine-sum families; §2 the loops `𝓛^{(1,2,3)}` of the carrier as fine sums; §3 the coordinates
`(block, offset)` of a fine vertex and the entries `M`, `S`, `W^{(k)}` in them; §4 the loops and the
twisted loops `twTrP`, `twLoopX` as sums over offsets; §5 the tie sums (`BAExp14b_twTie`,
`_twTie_ba`, probe `T2398Pins.lean:226`) and the block sums of `W^{(k)}` (`BAExp14b_Wk_blk`,
`W - 1 = lift(ω - 1)`); §6 permutations of nested sums; §7 the **block forms of the eight S2
families** (`BAExp14b_FD1t_block`, `_FD2t_`, `_FT2a_`, `_FT2b_`, `_FT3B_`, `_FT3CG_block`,
dispatched by `BAExp14b_FS2_block` and `BAExp14bS2Fam_block`): pathwise identities between the fine
sums of the families and block sums of `M^{(B)}`, `κ_k`, `X_{a₁}` and the loops `𝓛^{(2)}`,
`𝓛^{(3)}`, `twTrP`, `twLoopX = twL2'`, which L4b2 reads; §8 compiled checks and nonempty instances
of the block forms and of the pins.  Part B (`Graph/BAExp14bB.lean`) proves the identity.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false

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
      by_cases h3 : (split d L W x).1 = c <;> simp [h1, h2, h3]
    all_goals ring
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

private theorem BAExp14b_trace_prod2 {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Fin 2 → Matrix ι ι ℂ) :
    Matrix.trace (List.ofFn P).prod = ∑ x, ∑ y, P 0 x y * P 1 y x := by
  simp [List.ofFn_succ, Matrix.trace, Matrix.mul_apply]

/-- **`𝓛^{(2)}` as a double fine sum**: `tr(G(σ₁)E_a G(σ₂)E_b) = W^{-2d} Σ_{x ∈ [b]} Σ_{y ∈ [a]} G(σ₁)_{xy} G(σ₂)_{yx}`. -/
theorem BAExp14b_loop2 (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    loopFine d L W H z ![σ₁, σ₂] ![a, b] =
      (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W b, ∑ y ∈ Iblk d L W a, Gres H z σ₁ x y * Gres H z σ₂ y x := by
  rw [BAExp14b_loop_eq, BAExp14b_trace_prod2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.mul_diagonal, BAExp14b_dw]
  rw [Finset.mul_sum]
  simp only [Iblk, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : (split d L W x).1 = b
  · simp only [hx, ite_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : (split d L W y).1 = a <;> simp [hy]
    all_goals ring
  · simp [hx]

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

/-! ## 3. Coordinates `(block, offset)`: the entries of the carrier at the fine vertex `(c, o)`

A fine vertex is a pair `(c, o)` of a block `c ∈ Z_L^d` and an offset `o ∈ Fin (W^d)` (`splitEquiv`).  In these coordinates the ties of the
expansion are Kronecker deltas: `M_{(c,o),(c',o')} = 1[o = o'] M^{(B)}_{cc'}` (`BAMfine_eq`), `S_{(c,o),(c',o')} = t W^{-d} 1[c = c']`
(`BAlwS`), `(W - 1)_{(c,o),(c',o')} = W^{-d} (ω - 1)_{cc'}` (`BAExp14a_W_sub_one`) and `W^{(0)} = 1`. -/

section Coord

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The fine vertex of block `c` and offset `o`. -/
def BAExp14b_pt (c : Zd d L) (o : Fin (W ^ d)) : Idx d L W := (splitEquiv d L W).symm (c, o)

theorem BAExp14b_split_pt (c : Zd d L) (o : Fin (W ^ d)) : split d L W (BAExp14b_pt c o) = (c, o) :=
  (splitEquiv d L W).apply_symm_apply (c, o)

theorem BAExp14b_pt_split (x : Idx d L W) : BAExp14b_pt (split d L W x).1 (split d L W x).2 = x :=
  (splitEquiv d L W).symm_apply_apply x

theorem BAExp14b_pt_inj {c c' : Zd d L} {o o' : Fin (W ^ d)} :
    (BAExp14b_pt c o : Idx d L W) = BAExp14b_pt c' o' ↔ c = c' ∧ o = o' := by
  unfold BAExp14b_pt
  rw [(splitEquiv d L W).symm.injective.eq_iff]
  simp

/-- A sum over the fine lattice is a sum over `(block, offset)`. -/
theorem BAExp14b_sum_idx {β : Type*} [AddCommMonoid β] (F : Idx d L W → β) :
    ∑ x, F x = ∑ c : Zd d L, ∑ o : Fin (W ^ d), F (BAExp14b_pt c o) := by
  rw [← Equiv.sum_comp (splitEquiv d L W).symm F, Fintype.sum_prod_type]
  rfl

/-- A sum over the block `[a]` is a sum over the offsets. -/
theorem BAExp14b_sum_blk {β : Type*} [AddCommMonoid β] (a : Zd d L) (F : Idx d L W → β) :
    ∑ x ∈ Iblk d L W a, F x = ∑ o : Fin (W ^ d), F (BAExp14b_pt a o) := by
  simp only [Iblk, Finset.sum_filter]
  rw [BAExp14b_sum_idx]
  simp only [BAExp14b_split_pt]
  simp [Finset.sum_ite_eq']

end Coord

section CarrierEntries

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ)

/-- `M^{(B)}` of the carrier `baFMz sz z` at size `n`. -/
abbrev BAExp14b_MB : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) ((baFMz sz z).m n)

/-- `ω = Θ^{(+,+)}_t = (1 - t M^{(B)} ∘ M^{(B)})⁻¹` (`BATheta`), the kernel of `W = 1 + M⁺ S⁺`. -/
abbrev BAExp14b_om : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) ((baFMz sz z).m n) t true true

/-- The block kernel of `W^{(k)}`: `κ_0 = 1`, `κ_1 = ω - 1` (`Σ_{α ∈ [a₁]} W^{(k)}_{αw} = κ_k(a₁, [w])`, `BAExp14b_Wk_blk`). -/
def BAExp14b_kap (k : Bool) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  if k then BAExp14b_om sz z n t - 1 else 1

/-- **`M` at two fine vertices** (`BAMfine_eq`): `M_{(c,o),(c',o')} = 1[o = o'] M^{(B)}_{cc'}`. -/
theorem BAExp14b_M_pt (hm : 0 < ((baFMz sz z).m n).im) (c c' : Zd d (sz.L n)) (o o' : Fin (sz.W n ^ d)) :
    (baFMz sz z).M n (BAExp14b_pt c o) (BAExp14b_pt c' o') = if o = o' then BAExp14b_MB sz z n c c' else 0 := by
  have h := BAMfine_eq sz (BAflowLam0 sz z) (BAflowEs sz z) n hm (BAExp14b_pt c o) (BAExp14b_pt c' o')
  simp only [BAExp14b_split_pt] at h
  exact h

/-- **`S` at two fine vertices**: `S_{(c,o),(c',o')} = t W^{-d} 1[c = c']`. -/
theorem BAExp14b_S_pt (c c' : Zd d (sz.L n)) (o o' : Fin (sz.W n ^ d)) :
    BAlwS d (sz.L n) (sz.W n) t (BAExp14b_pt c o) (BAExp14b_pt c' o') =
      (t : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * if c = c' then 1 else 0) := by
  rw [BAExp14a_S_apply]
  simp only [BAExp14b_split_pt]

theorem BAExp14b_blk_pt (c : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)) : STblk sz n (BAExp14b_pt c o) = c := by
  simp [STblk, BAExp14b_split_pt]

variable {sz z n t}

/-- **`W^{(0)} = 1` at two fine vertices.** -/
theorem BAExp14b_Wk_pt_false (c c' : Zd d (sz.L n)) (o o' : Fin (sz.W n ^ d)) :
    BAExp14a_Wk sz z n t false (BAExp14b_pt c o) (BAExp14b_pt c' o') = if c = c' then (if o = o' then 1 else 0) else 0 := by
  simp only [BAExp14a_Wk, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, BAExp14b_pt_inj]
  by_cases h : c = c' <;> by_cases h' : o = o' <;> simp [h, h']

/-- **`W^{(1)} = W - 1 = lift(ω - 1)` at two fine vertices** (`BAExp14a_W_sub_one`, D402): `(W - 1)_{(c,o),(c',o')} = W^{-d} (ω - 1)_{cc'}`. -/
theorem BAExp14b_Wk_pt_true {κ : ℝ} (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (c c' : Zd d (sz.L n)) (o o' : Fin (sz.W n ^ d)) :
    BAExp14a_Wk sz z n t true (BAExp14b_pt c o) (BAExp14b_pt c' o') =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BAExp14b_om sz z n t - 1) c c' := by
  have h := BAExp14a_W_sub_one (W := sz.W n) (sz.three_le_L n) hr ht0 ht1
  have h2 := congrFun (congrFun h (BAExp14b_pt c o)) (BAExp14b_pt c' o')
  simp only [BAExp14a_Wk, ite_true]
  rw [h2]
  simp only [lwLift, Matrix.of_apply, BAExp14b_split_pt]

end CarrierEntries

/-! ## 4. The loops of the carrier and the twisted loops as sums over offsets -/

section LoopBridge

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- The resolvent of the flow matrix at charge `σ` is `twChg` of the carrier's `G` (`G(-) = G^*`, `lwWx_Gres_false`). -/
theorem BAExp14b_Gres_eq (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    Gres (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω) (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) σ x y =
      twChg ((baFMz sz z).G n t ω) σ x y := by
  cases σ
  · simp only [twChg, Bool.false_eq_true, ↓reduceIte]
    rw [lwWx_Gres_false (BAExpand_Hm_isHermitian sz n (BAflowLam0 sz z n) t ω)]
    rfl
  · rfl

/-- **`𝓛^{(2)}` of the carrier**: `𝓛^{(2)}_{(σ₁,σ₂),(a,b)} = W^{-2d} Σ_{x ∈ [b]} Σ_{y ∈ [a]} G(σ₁)_{xy} G(σ₂)_{yx}`. -/
theorem BAExp14b_L2_eq (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)) :
    (baFMz sz z).L n t ![σ₁, σ₂] ![a, b] ω =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) b, ∑ y ∈ Iblk d (sz.L n) (sz.W n) a,
        twChg ((baFMz sz z).G n t ω) σ₁ x y * twChg ((baFMz sz z).G n t ω) σ₂ y x := by
  change loopFine d (sz.L n) (sz.W n) (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω)
    (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) ![σ₁, σ₂] ![a, b] = _
  rw [BAExp14b_loop2]
  simp only [BAExp14b_Gres_eq]

/-- **`𝓛^{(3)}` of the carrier**: `𝓛^{(3)}_{(σ₁,σ₂,σ₃),(a,b,c)} = W^{-3d} Σ_{x ∈ [c]} Σ_{α ∈ [a]} Σ_{y ∈ [b]} G(σ₁)_{xα} G(σ₂)_{αy} G(σ₃)_{yx}`. -/
theorem BAExp14b_L3_eq (σ₁ σ₂ σ₃ : Bool) (a b c : Zd d (sz.L n)) :
    (baFMz sz z).L n t ![σ₁, σ₂, σ₃] ![a, b, c] ω =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 * ∑ x ∈ Iblk d (sz.L n) (sz.W n) c, ∑ α ∈ Iblk d (sz.L n) (sz.W n) a,
        ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, twChg ((baFMz sz z).G n t ω) σ₁ x α * twChg ((baFMz sz z).G n t ω) σ₂ α y *
          twChg ((baFMz sz z).G n t ω) σ₃ y x := by
  change loopFine d (sz.L n) (sz.W n) (BAExpand_Hm sz n (BAflowLam0 sz z n) t ω)
    (ztOf ((baFMz sz z).m n) (BAflowEs sz z n) t) ![σ₁, σ₂, σ₃] ![a, b, c] = _
  rw [BAExp14b_loop3]
  simp only [BAExp14b_Gres_eq]

end LoopBridge

section TwistCoord

variable {d : ℕ} {sz : Sizes d} {n : ℕ}

theorem BAExp14b_shift_pt (c a : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)) : twShift n c (BAExp14b_pt a o) = BAExp14b_pt c o := by
  unfold twShift
  rw [BAExp14b_split_pt]
  rfl

/-- **`Tr(X P_{c₁c₂})` as a sum over offsets**: `twTrP n X c₁ c₂ = W^{-d} Σ_o X_{(c₂,o),(c₁,o)}`. -/
theorem BAExp14b_twTrP_pt (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (c₁ c₂ : Zd d (sz.L n)) :
    twTrP n X c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ o : Fin (sz.W n ^ d), X (BAExp14b_pt c₂ o) (BAExp14b_pt c₁ o) := by
  unfold twTrP
  change _ * ∑ w ∈ Iblk d (sz.L n) (sz.W n) c₂, X w (twShift n c₁ w) = _
  rw [BAExp14b_sum_blk]
  simp only [BAExp14b_shift_pt]

/-- **`Tr(X₁ E_a X₂ P_{c₁c₂})` as a sum over offsets**: `twLoopX n X₁ X₂ a c₁ c₂ = W^{-2d} Σ_{o_x} Σ_{o_w} (X₂)_{(a,o_x),(c₁,o_w)} (X₁)_{(c₂,o_w),(a,o_x)}`. -/
theorem BAExp14b_twLoopX_pt (X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n X₁ X₂ a c₁ c₂ = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ ox : Fin (sz.W n ^ d), ∑ ow : Fin (sz.W n ^ d),
      X₂ (BAExp14b_pt a ox) (BAExp14b_pt c₁ ow) * X₁ (BAExp14b_pt c₂ ow) (BAExp14b_pt a ox) := by
  unfold twLoopX
  change _ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ w ∈ Iblk d (sz.L n) (sz.W n) c₁, X₂ x w * X₁ (twShift n c₂ w) x = _
  rw [BAExp14b_sum_blk]
  refine congrArg _ (Finset.sum_congr rfl fun ox _ => ?_)
  rw [BAExp14b_sum_blk]
  simp only [BAExp14b_shift_pt]

end TwistCoord

/-! ## 5. The tie sums and the block sums of `W^{(k)}` -/

/-! ## 6. Permutations of nested sums (helpers) -/

section Reorder

private theorem BAExp14b_rot4 {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ c, ∑ e, ∑ a, ∑ b, F a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ a, ∑ c, ∑ b, ∑ e, F a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ c, ∑ e, ∑ b, F a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, F a b c e := Finset.sum_comm
    _ = ∑ c, ∑ e, ∑ a, ∑ b, F a b c e := Finset.sum_congr rfl fun c _ => Finset.sum_comm

private theorem BAExp14b_rev3 {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] (F : ι₁ → ι₂ → ι₃ → ℂ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, F a b c := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- The last of three nested sums moves to the front. -/
private theorem BAExp14b_mf3 {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] (F : ι₁ → ι₂ → ι₃ → ℂ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm

/-- The last of four nested sums moves to the front. -/
private theorem BAExp14b_mf4 {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃] [Fintype ι₄] (F : ι₁ → ι₂ → ι₃ → ι₄ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ e, ∑ a, ∑ b, ∑ c, F a b c e := by
  calc ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ a, ∑ e, ∑ b, ∑ c, F a b c e :=
        Finset.sum_congr rfl fun a _ => BAExp14b_mf3 (F a)
    _ = ∑ e, ∑ a, ∑ b, ∑ c, F a b c e := Finset.sum_comm

end Reorder

/-! ## 7. The block forms of the eight S2 families (target 3)

Pathwise identities (no probability, no premise): the fine sum of each family of `BAExp14b_FS2` is a sum over blocks `a₁, c, c₁, c₂` of
`M^{(B)}`, `κ_k`, `X_{a₁}` and the loops `𝓛^{(2)}`, `𝓛^{(3)}` of the carrier, the twisted one-loop `twTrP`, the twisted two-loop `twLoopX`
(`= twL2'` with `G^σ = twChg G σ`; one slot carries `Ǧ = GM`).  With `x ∈ [a]`, `y ∈ [b]`, closing edge `G(σ)_{yx}`, `X_c = tr(Ǧ E_c)`.
L4b2 reads them through `BAExp14b_FS2_block`.  Proof of each: coordinates `(block, offset)` (§3), the Kronecker deltas of `M`, `S`, `W^{(k)}`,
a permutation of the nested sums (§6), `field_simp`. -/

section Blocks

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ} {ω : sz.SeqΩ} {κ : ℝ}

/-- Elimination of the Kronecker deltas of the ties in the coordinates `(block, offset)`, and of the free offsets (`Σ_o 1 = W^d`). -/
local macro "bf_elim" : tactic =>
  `(tactic| simp only [mul_ite, ite_mul, mul_zero, zero_mul, neg_ite, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, neg_zero, Finset.sum_const_zero, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow])

/-- Flatten the products `a * Σ`, `Σ * a` into one nest of sums. -/
local macro "bf_flat" : tactic => `(tactic| simp only [Finset.mul_sum, Finset.sum_mul])

/-- The last step of a block form: conjugates as `starRingEnd`, then clear the `W^d`. -/
local macro "bf_fin" : tactic => `(tactic| ((try simp only [star_mul', Complex.star_def]); field_simp))

/-- **`D1t` in block form**: `D1t = t Σ_{a₁,c} M^{(B)}_{aa₁} M^{(B)}_{a₁c} X_{a₁} · Tr(G^σ P_{ac}) · 𝓛^{(2)}_{(+,σ),(b,c)}`
(`lanlw` on `M_{xα} Ǧ_{αy}`, the `∂tail` child: `M_{xα}, M_{αα'}` put `x, α, α'` at one offset, `S_{α'β}` puts `β` in the block of `α'`). -/
theorem BAExp14b_FD1t_block (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FD1t sz z n t ω σ a b =
      (t : ℂ) * ∑ a₁, ∑ c, BAExp14b_MB sz z n a a₁ * BAExp14b_MB sz z n a₁ c * BAExp14a_X sz z n t ω a₁ *
        twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c * (baFMz sz z).L n t ![true, σ] ![b, c] ω := by
  have hm := hr.1.1
  unfold BAExp14b_FD1t BAExp14b_outerDt
  simp only [BAExp14b_L2_eq, BAExp14b_twTrP_pt]
  simp only [BAExp14b_sum_blk, BAExp14b_sum_idx, BAExp14b_M_pt sz z n hm, BAExp14b_S_pt, BAExp14b_blk_pt]
  cases σ <;>
  · simp only [BAExp14b_dtail, Bool.false_eq_true, ↓reduceIte, twChg]
    bf_elim
    bf_flat
    rw [BAExp14b_rot4]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => ?_
    rw [BAExp14b_rev3]
    refine Finset.sum_congr rfl fun o₁ _ => Finset.sum_congr rfl fun o₂ _ => Finset.sum_congr rfl fun o₃ _ => ?_
    try simp only [star_mul', Complex.star_def]
    ring

/-- **`D2t` in block form**: `D2t = t Σ_{a₁,c} M^{(B)}_{ac} M^{(B)}_{a₁b} X_{a₁} · Tr(G^σ P_{ac}) · L̃_{(σ,+),(c; a₁, b)}`, `L̃ = twL2'`
(`BAExp14b_twLoopX_twL2'`; `lanlw` on `Ǧ_{xα} M_{αy}`, the `∂tail` child; both loops uncircled). -/
theorem BAExp14b_FD2t_block (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FD2t sz z n t ω σ a b =
      (t : ℂ) * ∑ a₁, ∑ c, BAExp14b_MB sz z n a c * BAExp14b_MB sz z n a₁ b * BAExp14a_X sz z n t ω a₁ *
        twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c * twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) c a₁ b := by
  have hm := hr.1.1
  unfold BAExp14b_FD2t BAExp14b_outerDt
  simp only [BAExp14b_twLoopX_pt, BAExp14b_twTrP_pt]
  simp only [BAExp14b_sum_blk, BAExp14b_sum_idx, BAExp14b_M_pt sz z n hm, BAExp14b_S_pt, BAExp14b_blk_pt]
  cases σ <;>
  · simp only [BAExp14b_dtail, Bool.false_eq_true, ↓reduceIte, twChg]
    bf_elim
    bf_flat
    rw [BAExp14b_rot4]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => ?_
    rw [BAExp14b_rev3]
    refine Finset.sum_congr rfl fun o₁ _ => Finset.sum_congr rfl fun o₂ _ => Finset.sum_congr rfl fun o₃ _ => ?_
    try simp only [star_mul', Complex.star_def]
    ring

/-- **`T2a` in block form**: `T2a = Σ_{a₁,c} (ω - 1)_{a₁c} M^{(B)}_{ac} X_{a₁} · Tr(Ǧ E_b G^σ P_{ac})` (`(W - 1)_{αβ} Ǧ_{βy} M_{xβ}`; the circled leg is in
slot 1 of `twLoopX`). -/
theorem BAExp14b_FT2a_block (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FT2a sz z n t ω σ a b =
      ∑ a₁, ∑ c, (BAExp14b_om sz z n t - 1) a₁ c * BAExp14b_MB sz z n a c * BAExp14a_X sz z n t ω a₁ *
        twLoopX n ((baFMz sz z).GM n t ω) (twChg ((baFMz sz z).G n t ω) σ) b a c := by
  have hm := hr.1.1
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  unfold BAExp14b_FT2a BAExp14a_outer
  simp only [BAExp14b_twLoopX_pt]
  simp only [BAExp14b_sum_blk, BAExp14b_sum_idx, BAExp14b_M_pt sz z n hm, BAExp14b_Wk_pt_true hr ht0 ht1, BAExp14b_blk_pt]
  cases σ <;>
  · simp only [BAExp14a_tail, Bool.false_eq_true, ↓reduceIte, twChg, FlowFM.GM]
    bf_elim
    bf_flat
    rw [BAExp14b_rot4]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o₁ _ => Finset.sum_congr rfl fun o₂ _ => ?_
    bf_fin

/-- **`T2b` in block form**: `T2b = Σ_{a₁,c} (ω - 1)_{a₁c} M^{(B)}_{cb} X_{a₁} · Tr(G^σ E_a Ǧ P_{cb})` (`(W - 1)_{αβ} M_{βy} Ǧ_{xβ}`; the circled leg is
in slot 2 of `twLoopX`, the slot of `twCirc`). -/
theorem BAExp14b_FT2b_block (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FT2b sz z n t ω σ a b =
      ∑ a₁, ∑ c, (BAExp14b_om sz z n t - 1) a₁ c * BAExp14b_MB sz z n c b * BAExp14a_X sz z n t ω a₁ *
        twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c b := by
  have hm := hr.1.1
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  unfold BAExp14b_FT2b BAExp14a_outer
  simp only [BAExp14b_twLoopX_pt]
  simp only [BAExp14b_sum_blk, BAExp14b_sum_idx, BAExp14b_M_pt sz z n hm, BAExp14b_Wk_pt_true hr ht0 ht1, BAExp14b_blk_pt]
  cases σ <;>
  · simp only [BAExp14a_tail, Bool.false_eq_true, ↓reduceIte, twChg, FlowFM.GM]
    bf_elim
    bf_flat
    rw [BAExp14b_rot4]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun o₁ _ =>
      Finset.sum_congr rfl fun o₂ _ => ?_
    bf_fin

set_option maxHeartbeats 1600000 in
-- the coordinate expansion of a 7-fold sum with the Kronecker deltas of the ties (measured: fails at 400000, passes at 800000)
/-- **`T3B^{(k)}` in block form**: `T3B^{(k)} = t W^d Σ_{a₁,c₁,c₂} κ_k(a₁,c₁) M^{(B)}_{c₁c₂} X_{a₁} · Tr(Ǧ P_{c₁c₂}) · 𝓛^{(3)}_{(+,+,σ),(c₂,b,a)}`,
`Tr(Ǧ P_{c₁c₂}) = twTr C n t ω c₂ c₁` (`twTr_eq`): `W^{(k)}_{αw} M_{wγ} S_{γδ} Ǧ_{γw} G_{δy} G_{xδ}` (`Σ_{α ∈ [a₁]} W^{(k)}_{αw} = κ_k(a₁,[w])`). -/
theorem BAExp14b_FT3B_block (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (k σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FT3B sz z n t ω k σ a b =
      (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t k a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
        BAExp14a_X sz z n t ω a₁ * twTrP n ((baFMz sz z).GM n t ω) c₁ c₂ *
        (baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω := by
  have hm := hr.1.1
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  unfold BAExp14b_FT3B BAExp14a_outer
  simp only [BAExp14b_L3_eq, BAExp14b_twTrP_pt]
  simp only [BAExp14b_sum_blk, BAExp14b_sum_idx, BAExp14b_M_pt sz z n hm, BAExp14b_S_pt, BAExp14b_blk_pt]
  cases k
  · simp only [BAExp14b_Wk_pt_false, BAExp14b_kap, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
    cases σ <;>
    · simp only [BAExp14a_tail, Bool.false_eq_true, ↓reduceIte, twChg, FlowFM.GM]
      bf_elim
      bf_flat
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [BAExp14b_mf4]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      refine Finset.sum_congr rfl fun o₁ _ => ?_
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun o₂ _ => Finset.sum_congr rfl fun o₃ _ => Finset.sum_congr rfl fun o₄ _ => ?_
      bf_fin
  · simp only [BAExp14b_Wk_pt_true hr ht0 ht1, BAExp14b_kap, ↓reduceIte]
    cases σ <;>
    · simp only [BAExp14a_tail, Bool.false_eq_true, ↓reduceIte, twChg, FlowFM.GM]
      bf_elim
      bf_flat
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun c₁ _ => ?_
      rw [BAExp14b_mf4]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      refine Finset.sum_congr rfl fun o₁ _ => ?_
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun o₂ _ => Finset.sum_congr rfl fun o₃ _ => Finset.sum_congr rfl fun o₄ _ => ?_
      bf_fin

set_option maxHeartbeats 1600000 in
-- the coordinate expansion of a 7-fold sum with the Kronecker deltas of the ties (measured: fails at 400000, passes at 800000)
/-- **`T3C-Ḡ^{(k)}` in block form**: `T3C-Ḡ^{(k)} = t W^d Σ_{a₁,c₁,c₂} κ_k(a₁,c₁) M^{(B)}_{c₁c₂} X_{a₁} · 𝓛^{(2)}_{(+,σ),(b,c₂)} · Tr(G^σ E_a Ǧ P_{c₁c₂})`
(`W^{(k)}_{αw} M_{wγ} S_{γδ} G_{δy} Ǧ_{xw} ∂_{δγ}tail`; the circled leg is in slot 2 of `twLoopX`). -/
theorem BAExp14b_FT3CG_block (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (k σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FT3CG sz z n t ω k σ a b =
      (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t k a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
        BAExp14a_X sz z n t ω a₁ * (baFMz sz z).L n t ![true, σ] ![b, c₂] ω *
        twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c₁ c₂ := by
  have hm := hr.1.1
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  unfold BAExp14b_FT3CG BAExp14b_outerDt
  simp only [BAExp14b_L2_eq, BAExp14b_twLoopX_pt]
  simp only [BAExp14b_sum_blk, BAExp14b_sum_idx, BAExp14b_M_pt sz z n hm, BAExp14b_S_pt, BAExp14b_blk_pt]
  cases k
  · simp only [BAExp14b_Wk_pt_false, BAExp14b_kap, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
    cases σ <;>
    · simp only [BAExp14b_dtail, Bool.false_eq_true, ↓reduceIte, twChg, FlowFM.GM]
      bf_elim
      bf_flat
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [BAExp14b_mf4]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      refine Finset.sum_congr rfl fun o₁ _ => ?_
      rw [BAExp14b_mf3, BAExp14b_mf3]
      refine Finset.sum_congr rfl fun o₂ _ => Finset.sum_congr rfl fun o₃ _ => Finset.sum_congr rfl fun o₄ _ => ?_
      bf_fin
  · simp only [BAExp14b_Wk_pt_true hr ht0 ht1, BAExp14b_kap, ↓reduceIte]
    cases σ <;>
    · simp only [BAExp14b_dtail, Bool.false_eq_true, ↓reduceIte, twChg, FlowFM.GM]
      bf_elim
      bf_flat
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [BAExp14b_mf3]
      refine Finset.sum_congr rfl fun c₁ _ => ?_
      rw [BAExp14b_mf4]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      refine Finset.sum_congr rfl fun o₁ _ => ?_
      rw [BAExp14b_mf3, BAExp14b_mf3]
      refine Finset.sum_congr rfl fun o₂ _ => Finset.sum_congr rfl fun o₃ _ => Finset.sum_congr rfl fun o₄ _ => ?_
      bf_fin

end Blocks

section Dispatch

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)

/-- **The block forms of the eight S2 families**, in the order of `BAExp14b_FS2` (`D1t, D2t, T2a, T2b, T3B^{(0)}, T3B^{(1)}, T3C-Ḡ^{(0)}, T3C-Ḡ^{(1)}`),
`x ∈ [a]`, `y ∈ [b]`, closing edge `G(σ)_{yx}`; `G^σ = twChg G σ`, `Ǧ = GM`, `X_c = tr(Ǧ E_c)`, `MB = M^{(B)}`, `κ_0 = 1`, `κ_1 = ω - 1`. -/
def BAExp14b_BS2 (j : Fin 8) (σ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ![(t : ℂ) * ∑ a₁, ∑ c, BAExp14b_MB sz z n a a₁ * BAExp14b_MB sz z n a₁ c * BAExp14a_X sz z n t ω a₁ *
      twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c * (baFMz sz z).L n t ![true, σ] ![b, c] ω,
    (t : ℂ) * ∑ a₁, ∑ c, BAExp14b_MB sz z n a c * BAExp14b_MB sz z n a₁ b * BAExp14a_X sz z n t ω a₁ *
      twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c * twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) c a₁ b,
    ∑ a₁, ∑ c, (BAExp14b_om sz z n t - 1) a₁ c * BAExp14b_MB sz z n a c * BAExp14a_X sz z n t ω a₁ *
      twLoopX n ((baFMz sz z).GM n t ω) (twChg ((baFMz sz z).G n t ω) σ) b a c,
    ∑ a₁, ∑ c, (BAExp14b_om sz z n t - 1) a₁ c * BAExp14b_MB sz z n c b * BAExp14a_X sz z n t ω a₁ *
      twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c b,
    (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t false a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
      BAExp14a_X sz z n t ω a₁ * twTrP n ((baFMz sz z).GM n t ω) c₁ c₂ * (baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω,
    (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t true a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
      BAExp14a_X sz z n t ω a₁ * twTrP n ((baFMz sz z).GM n t ω) c₁ c₂ * (baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω,
    (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t false a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
      BAExp14a_X sz z n t ω a₁ * (baFMz sz z).L n t ![true, σ] ![b, c₂] ω *
      twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c₁ c₂,
    (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t true a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
      BAExp14a_X sz z n t ω a₁ * (baFMz sz z).L n t ![true, σ] ![b, c₂] ω *
      twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c₁ c₂] j

variable {sz z n t ω} {κ : ℝ}

/-- **The eight block forms** (target 3): `FS2 = BS2` for every family, charge and block pair, from the six lemmas above. -/
theorem BAExp14b_FS2_block (hr : BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (ht0 : 0 ≤ t) (ht1 : t < 1) (j : Fin 8) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FS2 sz z n t ω j σ a b = BAExp14b_BS2 sz z n t ω j σ a b := by
  fin_cases j
  · exact BAExp14b_FD1t_block hr σ a b
  · exact BAExp14b_FD2t_block hr σ a b
  · exact BAExp14b_FT2a_block hr ht0 ht1 σ a b
  · exact BAExp14b_FT2b_block hr ht0 ht1 σ a b
  · exact BAExp14b_FT3B_block hr ht0 ht1 false σ a b
  · exact BAExp14b_FT3B_block hr ht0 ht1 true σ a b
  · exact BAExp14b_FT3CG_block hr ht0 ht1 false σ a b
  · exact BAExp14b_FT3CG_block hr ht0 ht1 true σ a b

end Dispatch

/-! ## 8. Compiled checks and nonempty instances of the block forms and of the pins -/

end RBM.BA

end
