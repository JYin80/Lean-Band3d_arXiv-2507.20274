/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Pins

/-!
# The endpoints of the band model: Theorems 2.1, 2.2, 2.3, 2.4, 2.5

The five endpoint statements of the band model in the explicit form `W^τ`, `N^{-D}` of the paper,
the scalar and domain lemmas around them, two bridges to the universality statements, and compiled
nonempty instances.

* The vocabulary of Section 2.1: `calB` ((2.13) `eq:calBetaK`), `distB`, `Mband` (`M = m I`), the
  block averages `avg2`, the profiles `profPM`, `profPP`, the bounds `qdBound`, `qdBoundExp`, and
  the bad events.
* The four band endpoints in the explicit form: `decol` (Theorem 2.1 `MR:decol`), `locSC`
  (Theorem 2.2 `MR:locSC`), `QUE` (Theorem 2.3 `MR:QUE`), `QDiff` (Theorem 2.5 `MR:QuDiff`).
  `BUniv := UNBUniv` (Theorem 2.4 `Thm: B_Univ`) is the statement `UNBUniv` of `Universality/Pins`.
  Theorem 2.7 (the block Anderson model) is stated in `Main/FinalShape`.
* The explicit form and the stochastic domination `Prec` are compared by `explicit_of_stochDomAt`
  (any law `P`) and `explicit_of_prec`.
* The bridges `locSC → UNLocAvgBand` and `QUE → UNQueBand`.
* Compiled nonempty instances at `d = 3` on `SizesInst.sz0`, the edges of (2.10) `eq:WO` and the
  extreme inputs.

The five endpoint statements are proved from the flow outputs in `Main/ZTransfer`, `Main/FixedZ`,
`Main/ZNet`, `Main/QUEFromQDiff` and `Main/BandTerminal`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints

/-! ## 1. Vocabulary and the four band endpoints (explicit form) -/

section Endpoints

variable {d : ℕ}

/-- **`𝓑_{η,K}`** of (2.13) `eq:calBetaK`: `(lam² + η)⁻¹ / (W² (K + W)^{d-2}) + 1/(N η)`, `K ≥ 0`
a distance on the fine lattice, `N = (W L)^d = sz.size n`. -/
def calB (sz : Sizes d) (n : ℕ) (η K : ℝ) : ℝ :=
  (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) +
    (((sz.size n : ℕ) : ℝ) * η)⁻¹

/-- The paper's `W |a - b|` of (2.22) `eq:diffu1`, (2.23) `eq:diffu2`: `W` times the periodic `L^∞` distance of the
block lattice (Section 2, (2.3) `representativeL`).  For (2.14) `G_bound` the distance `|x - y|` is read as `distB` of the
block labels `[x], [y]` (with the paper's `L^∞` metric `zdistInf`, as in `STLocalEntry`); the literal fine-lattice
distance `K` satisfies `W (k - 1) ≤ K ≤ W (k + 1)`, `k = |[x]-[y]|_∞`, so `𝓑_{η,K} ≍ 𝓑_{η,Wk}` up to `2^{d-2}`. -/
def distB (sz : Sizes d) (n : ℕ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)

/-- `M_{xy}(z) = m(z) δ_{xy}` of (2.8) `eq:defMzsc`, `m = msc`. -/
def Mband (sz : Sizes d) (n : ℕ) (z : ℂ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if x = y then msc z else 0

/-- The block average `W^{-2d} ∑_{x∈[a], y∈[b]} F x y`. -/
def avg2 (sz : Sizes d) (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (a b : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y

/-- `Θ^{(+,-)}(z) = (1 - |m|² S^{(B)})⁻¹` ((2.21) `def:Theta`); `|m|² S^{(B)}` is `Theta`'s `ξ`. -/
def ThetaPM (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ)

/-- `Θ^{(+,+)}(z) = (1 - m² S^{(B)})⁻¹`. -/
def ThetaPP (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (msc z ^ 2)

/-- The profile of (2.22) `eq:diffu1`: `|m|² Θ^{(+,-)}_{ab} / W^d`. -/
def profPM (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * ThetaPM sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d

/-- The profile of (2.23) `eq:diffu2`: `m² Θ^{(+,+)}_{ab} / W^d`. -/
def profPP (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  msc z ^ 2 * ThetaPP sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d

/-- The right side of (2.22) `eq:diffu1`, (2.23) `eq:diffu2`: `W^τ [(𝓑_{η,0})^{1/5} 𝓑_{η,W|a-b|} ∧ (𝓑_{η,0})²]`. -/
def qdBound (sz : Sizes d) (n : ℕ) (τ η : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b))
    (calB sz n η 0 ^ 2)

/-- The right side of (2.24) `Meq:QdS1`, (2.25) `Meq:QdS2`: `W^τ (𝓑_{η,0})² ((lam² W^d)^{-1/5} + 𝓑_{η,0})`. -/
def qdBoundExp (sz : Sizes d) (n : ℕ) (τ η : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n η 0 ^ 2 *
    ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 : ℝ) / 5) + calB sz n η 0)

/-- The failure event of (2.11) `eq:psikLinfty`: some orthonormal eigenbasis has a bulk eigenvector with
`‖ψ_k‖²_∞ > N^{-1+τ}`. -/
def decolBad (sz : Sizes d) (n : ℕ) (κ τ : ℝ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqXmat n ω) μ ψ → ∀ k, |μ k| ≤ 2 - κ → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)

/-- The failure event of (2.14) `G_bound` at one `z`: some `x, y` with `|G_xy(z) - M_xy(z)|² > W^τ 𝓑_{η,|x-y|}`,
`|x-y|` read as `W |[x]-[y]|_∞` (`distB`). -/
def locBad1z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n),
    ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
      ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2

/-- The failure event of (2.15) `G_bound_ave` at one `z`. -/
def locBad2z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z‖

/-- The failure event of (2.22) `eq:diffu1` at one `z`, the blocks `a, b` inside. -/
def qd1Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n z a b‖

/-- The failure event of (2.23) `eq:diffu2` at one `z`. -/
def qd2Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b - profPP sz n z a b‖

/-- The failure event of (2.14) `G_bound`: some `z ∈ 𝐃_{κ,ε}` fails.  The union over `z` is **inside** the
probability. -/
def locBad1 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad1z sz τ n z ω

/-- The failure event of (2.15) `G_bound_ave`, the union over `z` inside. -/
def locBad2 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad2z sz τ n z ω

/-- The failure event of (2.22) `eq:diffu1`, the union over `z` and the blocks `a, b` inside. -/
def qd1Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd1Badz sz τ n z ω

/-- The failure event of (2.23) `eq:diffu2`. -/
def qd2Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd2Badz sz τ n z ω

/-- The failure event of (2.19) `Meq:QUE2` for a set `A` of blocks: some orthonormal eigenbasis
has a `k` in the window with `|∑_{a∈A}∑_{x∈[a]}|ψ_k(x)|² - W^d|A|/N| ≥ W^{d-c}|A|/N`.  The first half
(2.18) `Meq:QUE` is `queBadMat`. -/
def que2BadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (A : Finset (Zd d L))
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ k, queWindow d L W lam ε₀ E (μ k) ∧
      (W : ℝ) ^ ((d : ℝ) - c) * (A.card : ℝ) / (((W * L) ^ d : ℕ) : ℝ) ≤
        |(∑ a ∈ A, ∑ x ∈ Iblk d L W a, ‖ψ k x‖ ^ 2) -
            (W : ℝ) ^ d / (((W * L) ^ d : ℕ) : ℝ) * (A.card : ℝ)|

/-- **`decol`**: Theorem 2.1 (`MR:decol`) for the band model.  Constants `(d, 𝔠, 𝔡)` before the sequence
`sz` (whose field `sz.lam` is the coupling parameter of (2.1) `def:ilambda`); `Admissible` is `0 < 𝔠, 𝔡`, `N → ∞`,
(2.9) `Main_DEL_COND`, (2.10) `eq:WO`; then `(κ, τ, D)`, then `∀ᶠ n`. -/
def decol : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | decolBad sz n κ τ ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`locSC`**: Theorem 2.2 (`MR:locSC`): (2.14) `G_bound` and (2.15) `G_bound_ave`, each with probability
`≥ 1 - N^{-D}`, the union over `z` inside. -/
def locSC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`QUE`**: Theorem 2.3 (`MR:QUE`): (2.18) `Meq:QUE` and (2.19) `Meq:QUE2` (`A ≠ ∅`), uniformly
in `|E| ≤ 2 - κ`, the block `a` and the set `A` (the `N₀` is uniform, the paper's `sup_E max_a`).  The window is
`𝓘_E(ε₀)` of (2.17) `eq:defIE` with `lam` (the footnote after (2.11) `eq:psikLinfty`: `lam ∧ 1` only beyond (2.10) `eq:WO`). -/
def QUE : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
        (∀ a : Zd d (sz.L n),
          Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ) ∧
        (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
          Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ)

/-- **`QDiff`**: Theorem 2.5 (`MR:QuDiff`): (2.22) `eq:diffu1`, (2.23) `eq:diffu2` with probability `≥ 1 - N^{-D}`
(the union over `z` inside; the paper's "for all `a, b`" is read with `a, b` inside the probability too: a union bound over
`L^{2d} ≤ N²` pairs), and (2.24) `Meq:QdS1`, (2.25) `Meq:QdS2` for each `z ∈ 𝐃_{κ,ε}` with `N₀`
uniform over `𝐃_{κ,ε}`. -/
def QDiff : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      (Sizes.seqP sz {ω | qd1Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, sz.locDomain κ ε n z → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im

/-- **`BUniv`**: Theorem 2.4 (`Thm: B_Univ`) is the statement `UNBUniv` of `Universality/Pins`. -/
abbrev BUniv : Prop := UNBUniv

end Endpoints


/-! ## 2. Scalar facts: `𝓑_{η,K}` against `Bctl`, `STWB`, and the lower bound `(Nη)⁻¹` -/

section Scalars

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem W_pos_real : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n

private theorem L_pos_real : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
  have := sz.three_le_L n
  exact_mod_cast (by omega : 0 < sz.L n)

private theorem size_cast : ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d := by
  simp [Sizes.size]

/-- **`𝓑_{η,0} = W^{-d} B_{1-η,0}`** ((2.63) `eq:BtBt` at `t = 1 - η`, equality): the bound
`sz.Bctl n (1 - η)` of the stochastic chain is the paper's `𝓑_{η,0}`.  Needs `d ≥ 2` (`W² W^{d-2} = W^d`). -/
theorem calB_zero_eq_Bctl (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) :
    calB sz n η 0 = sz.Bctl n (1 - η) := by
  have hW := W_pos_real sz n
  have hL := L_pos_real sz n
  have hlam : 0 < sz.lam n ^ 2 + η := by positivity
  have hWd : ((sz.W n : ℕ) : ℝ) ^ 2 * (0 + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) = ((sz.W n : ℕ) : ℝ) ^ d := by
    rw [zero_add, ← pow_add]; congr 1; omega
  have habs : |1 - (1 - η)| = η := by rw [sub_sub_cancel, abs_of_pos hη]
  unfold calB Sizes.Bctl Bparam
  rw [habs, hWd, size_cast sz n, mul_pow]
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  field_simp

/-- **`𝓑_{η,Wk} = W^{-d} B_{1-η,k}`** for a block distance `k`: this is `STWB` of the loop estimates
(`Induction/Defs`); the factor `W` in `(K + W)` is the block unit. -/
theorem calB_blk_eq_STWB (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    calB sz n η (((sz.W n : ℕ) : ℝ) * (k : ℝ)) = STWB sz n (1 - η) k := by
  have hW := W_pos_real sz n
  have hL := L_pos_real sz n
  have hlam : 0 < sz.lam n ^ 2 + η := by positivity
  have hk : 0 < ((k : ℝ) + 1) := by positivity
  have hWd : ((sz.W n : ℕ) : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) * (k : ℝ) + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)
      = ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) + 1) ^ (d - 2) := by
    have : ((sz.W n : ℕ) : ℝ) * (k : ℝ) + ((sz.W n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) * ((k : ℝ) + 1) := by ring
    rw [this, mul_pow, ← mul_assoc, ← pow_add]
    congr 2; omega
  have habs : |1 - (1 - η)| = η := by rw [sub_sub_cancel, abs_of_pos hη]
  unfold calB STWB Bparam
  rw [habs, hWd, size_cast sz n, mul_pow]
  field_simp

/-- `(N η)⁻¹ ≤ 𝓑_{η,K}` for `η > 0`, `K ≥ 0`: the floor of the bound (absorbs the additive `W^{-D}` of
(2.75) `Eq:Gdecay` and the net error). -/
theorem inv_size_mul_le_calB (hd : 2 ≤ d) {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) :
    (((sz.size n : ℕ) : ℝ) * η)⁻¹ ≤ calB sz n η K := by
  have hW := W_pos_real sz n
  have hlam : 0 < sz.lam n ^ 2 + η := by positivity
  unfold calB
  have : 0 ≤ (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) := by
    have : 0 ≤ K + ((sz.W n : ℕ) : ℝ) := by linarith
    positivity
  linarith

theorem calB_nonneg {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) : 0 ≤ calB sz n η K := by
  have hW := W_pos_real sz n
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : 0 < K + ((sz.W n : ℕ) : ℝ) := by linarith
  unfold calB
  positivity

end Scalars


/-! ## 3. The explicit `W^τ`, `N^{-D}` form against the stochastic domination `Prec` -/

section Form

variable {d : ℕ} (sz : Sizes d)

/-- **`StochDomAt` ⟹ explicit, for any law** (the bridge needed by the block Anderson endpoints and by the band
assembly): from `≺` at the scale `N^τ` (union inside) for an arbitrary probability space `(Ω, P)`, and `W ≥ N^𝔠`
(`Bandwidth`), the paper's `W^τ` form with `N^{-D}`: `N^{𝔠τ} ≤ W^τ` (`size_rpow_le_W_rpow`).  Needs `ζ ≥ 0`
(the bounds are `≥ 0`) and no `N → ∞`.  The block Anderson law is `seqP (sz.withLam 0)`, so the lemma is stated for
every `P`. -/
theorem explicit_of_stochDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → Ω → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hb : sz.Bandwidth 𝔠) (h : StochDomAt P sz.size ξ ζ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ n in atTop, P {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D)) := by
  filter_upwards [h (𝔠 * τ) (mul_pos h𝔠 hτ) D hD, hb] with n hn hbn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * τ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ := by
    rw [Real.rpow_mul (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hbn hτ.le
  exact mul_le_mul_of_nonneg_right h1 (hζ n u ω)

/-- **`Prec` ⟹ explicit** (the band law `seqP sz`): `explicit_of_stochDomAt` at `P = seqP sz`. -/
theorem explicit_of_prec {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hb : sz.Bandwidth 𝔠) (h : sz.Prec ξ ζ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) :
    ∀ᶠ n in atTop, Sizes.seqP sz {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D)) :=
  explicit_of_stochDomAt sz (Sizes.seqP sz) h𝔠 hζ hb h hτ hD

/-- **Sections ⟹ eventually for all** (the diagonal argument that turns `UNMLOut`, which is stated along
sequences `z : ℕ → ℂ`, into a statement with `N₀` uniform over `𝐃_{κ,ε}`).  This is the argument of RBM2D
`EndpointsFromSTO_eventually_forall_of_sections` (RBM1D `eventually_forall_of_forall_sequences`). -/
theorem eventually_forall_of_sections {Z : ℕ → Type*} (hne : ∀ n, Nonempty (Z n))
    {Q : ∀ n, Z n → Prop} (h : ∀ s : ∀ n, Z n, ∀ᶠ n in atTop, Q n (s n)) :
    ∀ᶠ n in atTop, ∀ z : Z n, Q n z := by
  classical
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  let s : ∀ n, Z n := fun n => if hb : ∃ z, ¬ Q n z then hb.choose else (hne n).some
  have hfreq : ∃ᶠ n in atTop, ¬ Q n (s n) := by
    refine hnot.mono fun n hn => ?_
    have hb : ∃ z, ¬ Q n z := by
      by_contra hb
      push Not at hb
      exact hn hb
    simp only [s, hb, dite_true]
    exact hb.choose_spec
  obtain ⟨n, hn, hQ⟩ := (hfreq.and_eventually (h s)).exists
  exact hn hQ

/-- **A deterministic `Prec` is a deterministic bound** (the expectation half (2.24) `Meq:QdS1`, (2.25) `Meq:QdS2`: the left
side `|𝔼 𝓛 - 𝒦|` of `STExp2` does not depend on `ω`): `P(univ) = 1 > N^{-1}`, so for `N > 1` the bad set is empty. -/
theorem det_of_prec (hsz : sz.SizeTendsto) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω ω', ξ n u ω = ξ n u ω') (hζ : ∀ n u ω ω', ζ n u ω = ζ n u ω')
    (h : sz.Prec ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
  filter_upwards [h τ hτ 1 one_pos, hsz.eventually_gt_atTop 1] with n hn hN1
  intro u ω
  by_contra hlt
  push Not at hlt
  have huniv : badSetAt sz.size ξ ζ τ n = Set.univ := by
    ext ω'
    simp only [Set.mem_univ, iff_true]
    exact ⟨u, by rw [hζ n u ω' ω, hξ n u ω' ω]; exact hlt⟩
  rw [huniv, measure_univ] at hn
  have hlt1 : ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    have : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) = (((sz.size n : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    rw [this]
    exact inv_lt_one_of_one_lt₀ hN1
  exact absurd hn (not_le.mpr hlt1)

end Form


/-! ## 4. The domain lemmas for `𝐃_{κ,ε}` and the positivity of `𝓑` -/

section Domain

variable {d : ℕ}

theorem STWB_nonneg (sz : Sizes d) (n : ℕ) (u : ℝ) (k : ℕ) : 0 ≤ STWB sz n u k := by
  unfold STWB Bparam
  positivity

theorem Nsz_pos (sz : Sizes d) (n : ℕ) : (0 : ℝ) < Nsz sz n := by
  have := one_le_size sz n
  exact_mod_cast (by omega : 0 < sz.size n)

/-- The domain `𝐃_{κ,ε}` has `0 < Im z`. -/
theorem locDomain_im_pos {sz : Sizes d} {κ ε : ℝ} {n : ℕ} {z : ℂ} (h : sz.locDomain κ ε n z) : 0 < z.im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (Nsz_pos sz n) _) h.2.1

/-- `𝐃_{κ,ε}` is nonempty (`z = i`) when `κ ≤ 2`, `ε ≤ 1`: the extreme `κ = 2`, `ε = 1` is the single point `i`;
for `κ > 2` or `ε > 1` (and `N > 1`) it is empty. -/
theorem locDomain_nonempty (sz : Sizes d) {κ ε : ℝ} (hκ : κ ≤ 2) (hε : ε ≤ 1) (n : ℕ) :
    ∃ z : ℂ, sz.locDomain κ ε n z := by
  refine ⟨Complex.I, ?_, ?_, by simp⟩
  · simp only [Complex.I_re, abs_zero]; linarith
  · simp only [Complex.I_im]
    have h1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast one_le_size sz n
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)

theorem locDomain_empty_kappa (sz : Sizes d) {κ ε : ℝ} (hκ : 2 < κ) (n : ℕ) (z : ℂ) :
    ¬ sz.locDomain κ ε n z := by
  intro h
  have := h.1
  have := abs_nonneg z.re
  linarith

theorem locDomain_empty_eps (sz : Sizes d) {κ ε : ℝ} (hε : 1 < ε) {n : ℕ} (hN : 1 < Nsz sz n) (z : ℂ) :
    ¬ sz.locDomain κ ε n z := by
  intro h
  have h1 := h.2.1
  have h2 := h.2.2
  have := Real.one_lt_rpow hN (by linarith : 0 < -1 + ε)
  linarith

end Domain


/-! ## 5. The bridges to the universality statements (`locSC → UNLocAvgBand`, `QUE → UNQueBand`) -/

section Bridges

/-- **`locSC → UNLocAvgBand`**: the second half of `locSC` ((2.15) `G_bound_ave`, union over `z` inside) is the
statement `UNLocAvgBand`; the only rewriting is `𝓑_{η,0} = sz.Bctl n (1 - η)` under the binder (`calB_zero_eq_Bctl`,
`0 < Im z` from `locDomain`), because that statement keeps the paper's `𝓑`. -/
theorem locSC_to_UNLocAvgBand : locSC → UNLocAvgBand := by
  intro h d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  filter_upwards [(h d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD)] with n hn
  refine le_trans (measure_mono ?_) hn.2
  rintro ω ⟨z, hz, a, ha⟩
  refine ⟨z, hz, a, ?_⟩
  rw [calB_zero_eq_Bctl sz n (by omega) (locDomain_im_pos hz)]
  exact ha

/-- **`QUE → UNQueBand`**: the first half (2.18) `Meq:QUE` is a projection (the events and the bound are
`queBadMat`, `queBound`). -/
theorem QUE_to_UNQueBand : QUE → UNQueBand := by
  intro h d hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6
  exact (h d hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6).mono fun n hn E hE a => (hn E hE).1 a

end Bridges


/-! ## 6. Compiled nonempty instances at `d = 3` on `SizesInst.sz0` and extreme inputs

Data: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`,
`N = 2097152`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`; `locSC`, `QDiff`: `ε = 1/20`, `τ = 1/10`, `D = 2`; `decol`: `τ = 1/10`, `D = 1`;
`QUE`: `ε₀ = 1/30`, `c = 1/60`, `τ = 1/10` (`0 < ε₀ < 𝔡/2 = 1/20`, `0 < c < ε₀ ∧ 𝔡/5 = 1/50`).  The endpoints are
hypotheses of the theorems `inst_decol`, `inst_locSC`, `inst_QUE`, `inst_QDiff`, `inst_BUniv`,
`inst_bridge_loc`, `inst_bridge_que`, which apply each endpoint with every deterministic hypothesis
(`3 ≤ d`, `Admissible`, the positivity of the constants and the ranges of `ε₀, c`) discharged. -/

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- **`decol` (Theorem 2.1)** at the instance. -/
theorem inst_decol (h : decol) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)

/-- **`locSC` (Theorem 2.2)** at the instance. -/
theorem inst_locSC (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **`QUE` (Theorem 2.3)** at the instance: `ε₀ = 1/30`, `c = 1/60`, `τ = 1/10`. -/
theorem inst_QUE (h : QUE) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
      (∀ a : Zd 3 (sz0.L n),
        Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) ∧
      (∀ A : Finset (Zd 3 (sz0.L n)), A.Nonempty →
        Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E A (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (by norm_num) (1 / 30) (1 / 60) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **`QDiff` (Theorem 2.5)** at the instance (the probability half and the expectation half). -/
theorem inst_QDiff (h : QDiff) :
    ∀ᶠ n in atTop,
      (Sizes.seqP sz0 {ω | qd1Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z → ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **`BUniv` (Theorem 2.4)** at the instance (`UNBUniv`): `k = 1`, `E = 0`, `𝒪 = bump`. -/
theorem inst_BUniv (h : BUniv) :
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible 1 le_rfl (1 / 10) (by norm_num) 0 (by norm_num) bump bump_testFun

/-- **Bridge `locSC → UNLocAvgBand`** at the instance. -/
theorem inst_bridge_loc (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | ∃ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z ∧ ∃ a : Zd 3 (sz0.L n),
          ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * sz0.Bctl n (1 - z.im) <
            ‖(((sz0.W n : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (sz0.L n) (sz0.W n) a,
                Gres (Sizes.seqXmat sz0 n ω) z true x x - msc z‖} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  locSC_to_UNLocAvgBand h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **Bridge `QUE → UNQueBand`** at the instance. -/
theorem inst_bridge_que (h : QUE) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 → ∀ a : Zd 3 (sz0.L n),
      Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
        queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10) :=
  QUE_to_UNQueBand (h) 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (by norm_num) (1 / 30) (1 / 60) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)


/-! ### The edges of (2.10) `eq:WO`: `lam = W^{-d/2+𝔡}` and `lam = 𝔡⁻¹` -/

/-! ### Extreme inputs -/

end Inst

end RBM.Endpoints
