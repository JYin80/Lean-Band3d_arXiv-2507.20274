/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Pins

/-!
# MA-01: the endpoint freeze of the band model (Theorems 2.1, 2.2, 2.3, 2.4, 2.5)

Ticket T2210 (MA-01 of the T2192 assembly split).  The vocabulary, the endpoint pins, the scalar and
form lemmas, the domain lemmas, the UN bridges and the MA-01 instances are moved verbatim from the
compiled probe `RBM3D/Probe/T2192Pins.lean` at `97d958e` (branch `t/T2192`, never merged).
The probe namespace `RBM.Probe.T2192` becomes `RBM.Endpoints`, its `Inst` becomes
`RBM.Endpoints.Inst`.

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`).

* The vocabulary of `1_2`: `calB` (`(eq:calBetaK)`), `distB`, `Mband` (`M = m I`), the block
  averages `avg2`, the profiles `profPM`, `profPP`, the bounds `qdBound`, `qdBoundExp`, and the
  bad events.
* The four band endpoints in the explicit form `W^τ`, `N^{-D}` of the paper: `decol` (Thm 2.1),
  `locSC` (Thm 2.2), `QUE` (Thm 2.3), `QDiff` (Thm 2.5).  `BUniv := UNBUniv` (Thm 2.4, the merged UN
  pin).  Theorem 2.7 is not stated here: it stays with the BA gate.
* The explicit form and the merged `Prec` are equivalent (D504): `explicit_of_stochDomAt` (any law
  `P`), `explicit_of_prec`, `prec_of_explicit`.  The reading notes cited in the moved docstrings as
  `T2192a`, `T2192b`, `T2192d` are D500, D501, D503 of `docs/paper-deltas.md`.
* The UN bridges `locSC → UNLocAvgBand` and `QUE → UNQueBand`.
* Compiled nonempty instances at `d = 3` on `SizesInst.sz0`, the `(eq:WO)` edges and the extreme
  inputs (CLAUDE.md §4 step 2).

The assembly chain that proves the pins from the flow outputs is MA-02 ... MA-06 (`Main/ZTransfer`,
`Main/FixedZ`, `Main/ZNet`, `Main/QUEFromQDiff`, `MainTheorems`).  The five endpoint `Prop`s are
registered as owed in `RBM3D/Test/Axioms.lean`.
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

/-- **`𝓑_{η,K}`** of `(eq:calBetaK)` (`1_2:384`): `(ilambda² + η)⁻¹ / (W² (K + W)^{d-2}) + 1/(N η)`, `K ≥ 0`
a distance on the fine lattice, `N = (W L)^d = sz.size n`.  T2001 `calB` (`bd95cc9:RBM3D/Probe/T2001Endpoints.lean:99`),
T2161 `BAcalB` (`82e72b3:RBM3D/Probe/T2161Pins.lean:1483`, the same expression: script comparison in the portmap). -/
def calB (sz : Sizes d) (n : ℕ) (η K : ℝ) : ℝ :=
  (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) +
    (((sz.size n : ℕ) : ℝ) * η)⁻¹

/-- The paper's `W |a - b|` of `(eq:diffu1)`, `(eq:diffu2)`: `W` times the periodic `L^∞` distance of the
block lattice (`1_2:274`).  For `(G_bound)` the distance `|x - y|` of `1_2:388` is read as `distB` of the block labels
`[x], [y]` (T2001e, with the paper's `L^∞` metric, `zdistInf`: as the merged `STLocalEntry`); the literal fine-lattice
distance `K` satisfies `W (k - 1) ≤ K ≤ W (k + 1)`, `k = |[x]-[y]|_∞`, so `𝓑_{η,K} ≍ 𝓑_{η,Wk}` up to `2^{d-2}`
(report, paper-delta candidate `T2192b`). -/
def distB (sz : Sizes d) (n : ℕ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)

/-- `M_{xy}(z) = m(z) δ_{xy}` of `(eq:defMzsc)` (`1_2:343`), `m = msc` (`msc_eq_integral`, T2001h). -/
def Mband (sz : Sizes d) (n : ℕ) (z : ℂ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if x = y then msc z else 0

/-- The block average `W^{-2d} ∑_{x∈[a], y∈[b]} F x y`. -/
def avg2 (sz : Sizes d) (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (a b : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y

/-- `Θ^{(+,-)}(z) = (1 - |m|² S^{(B)})⁻¹` (`def:Theta`, `1_2:472`); `|m|² S^{(B)}` is `Theta`'s `ξ`. -/
def ThetaPM (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ)

/-- `Θ^{(+,+)}(z) = (1 - m² S^{(B)})⁻¹`. -/
def ThetaPP (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (msc z ^ 2)

/-- The profile of `(eq:diffu1)`: `|m|² Θ^{(+,-)}_{ab} / W^d`. -/
def profPM (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * ThetaPM sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d

/-- The profile of `(eq:diffu2)`: `m² Θ^{(+,+)}_{ab} / W^d`. -/
def profPP (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  msc z ^ 2 * ThetaPP sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d

/-- The right side of `(eq:diffu1)`, `(eq:diffu2)`: `W^τ [(𝓑_{η,0})^{1/5} 𝓑_{η,W|a-b|} ∧ (𝓑_{η,0})²]`. -/
def qdBound (sz : Sizes d) (n : ℕ) (τ η : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b))
    (calB sz n η 0 ^ 2)

/-- The right side of `(Meq:QdS1)`, `(Meq:QdS2)`: `W^τ (𝓑_{η,0})² ((ilambda² W^d)^{-1/5} + 𝓑_{η,0})`. -/
def qdBoundExp (sz : Sizes d) (n : ℕ) (τ η : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n η 0 ^ 2 *
    ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 : ℝ) / 5) + calB sz n η 0)

/-- The failure event of `(eq:psikLinfty)`: some orthonormal eigenbasis has a bulk eigenvector with
`‖ψ_k‖²_∞ > N^{-1+τ}` (`T2001` `DecolBad`, RBM2D `decolEvent`, `RBM2D/Endpoints.lean:81`). -/
def decolBad (sz : Sizes d) (n : ℕ) (κ τ : ℝ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqXmat n ω) μ ψ → ∀ k, |μ k| ≤ 2 - κ → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)

/-- The failure event of `(G_bound)` at one `z`: some `x, y` with `|G_xy(z) - M_xy(z)|² > W^τ 𝓑_{η,|x-y|}`,
`|x-y|` read as `W |[x]-[y]|_∞` (`distB`). -/
def locBad1z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n),
    ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
      ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2

/-- The failure event of `(G_bound_ave)` at one `z`. -/
def locBad2z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z‖

/-- The failure event of `(eq:diffu1)` at one `z`, the blocks `a, b` inside. -/
def qd1Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n z a b‖

/-- The failure event of `(eq:diffu2)` at one `z`. -/
def qd2Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b - profPP sz n z a b‖

/-- The failure event of `(G_bound)` (`1_2:388`): some `z ∈ 𝐃_{κ,ε}` fails.  The union over `z` is **inside** the
probability (T2001b). -/
def locBad1 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad1z sz τ n z ω

/-- The failure event of `(G_bound_ave)` (`1_2:391`), `∩_z` inside. -/
def locBad2 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad2z sz τ n z ω

/-- The failure event of `(eq:diffu1)`, `∩_z` and the blocks `a, b` inside. -/
def qd1Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd1Badz sz τ n z ω

/-- The failure event of `(eq:diffu2)`. -/
def qd2Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd2Badz sz τ n z ω

/-- The failure event of `(Meq:QUE2)` for a set `A` of blocks (`1_2:417`): some orthonormal eigenbasis
has a `k` in the window with `|∑_{a∈A}∑_{x∈[a]}|ψ_k(x)|² - W^d|A|/N| ≥ W^{d-c}|A|/N`.  `T2001` `Que2Bad`,
T2161 `BAque2Bad`; the first half `(Meq:QUE)` is the merged `queBadMat`. -/
def que2BadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (A : Finset (Zd d L))
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ k, queWindow d L W lam ε₀ E (μ k) ∧
      (W : ℝ) ^ ((d : ℝ) - c) * (A.card : ℝ) / (((W * L) ^ d : ℕ) : ℝ) ≤
        |(∑ a ∈ A, ∑ x ∈ Iblk d L W a, ‖ψ k x‖ ^ 2) -
            (W : ℝ) ^ d / (((W * L) ^ d : ℕ) : ℝ) * (A.card : ℝ)|

/-- **Pin `MR:decol`** (Theorem 2.1, `1_2:357-370`), band model.  Constants `(d, 𝔠, 𝔡)` before the sequence
`sz` (which carries `ilambda` as the sequence `sz.lam`); `Admissible` is `0 < 𝔠, 𝔡`, `N → ∞`,
`(Main_DEL_COND)`, `(eq:WO)`; then `(κ, τ, D)`, then `∀ᶠ n`.  Registry class: **owed** (MA). -/
def decol : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | decolBad sz n κ τ ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **Pin `MR:locSC`** (Theorem 2.2, `1_2:386-395`): `(G_bound)` and `(G_bound_ave)`, each with probability
`≥ 1 - N^{-D}`, `∩_z` inside (T2001b).  Registry class: **owed** (MA). -/
def locSC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **Pin `MR:QUE`** (Theorem 2.3, `1_2:406-420`): `(Meq:QUE)` and `(Meq:QUE2)` (`A ≠ ∅`, T2001f), uniformly
in `|E| ≤ 2 - κ`, the block `a` and the set `A` (the `N₀` is uniform, the paper's `sup_E max_a`).  The window is
`𝓘_E(ε₀)` of `(eq:defIE)` with `lam` (footnote `1_2:372`: `lam ∧ 1` only beyond `(eq:WO)`).  Registry
class: **owed** (MA). -/
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

/-- **Pin `MR:QuDiff`** (Theorem 2.5, `1_2:488-511`): `(eq:diffu1)`, `(eq:diffu2)` with probability `≥ 1 - N^{-D}`
(`∩_z` inside, T2001b; the paper's "for all `a, b`" is read with `a, b` inside the probability too: a union bound over
`L^{2d} ≤ N²` pairs, paper-delta candidate `T2192d`), and `(Meq:QdS1)`, `(Meq:QdS2)` for each `z ∈ 𝐃_{κ,ε}` with `N₀`
uniform over `𝐃_{κ,ε}` (paper-delta candidate `T2192a`).  Registry class: **owed** (MA). -/
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

/-- **`Thm: B_Univ`** (Theorem 2.4) is the merged UN pin, not re-pinned (`Universality/Pins.lean:177`). -/
abbrev BUniv : Prop := UNBUniv

end Endpoints


/-! ## 2. Scalar facts: `𝓑_{η,K}` against the merged `Bctl`, `STWB`, and the lower bound `(Nη)⁻¹` -/

section Scalars

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem W_pos_real : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n

private theorem L_pos_real : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
  have := sz.three_le_L n
  exact_mod_cast (by omega : 0 < sz.L n)

private theorem size_cast : ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d := by
  simp [Sizes.size]

/-- **`𝓑_{η,0} = W^{-d} B_{1-η,0}`** (`(eq:BtBt)` at `t = 1 - η`, equality): the merged control
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

/-- **`𝓑_{η,Wk} = W^{-d} B_{1-η,k}`** for a block distance `k`: the merged `STWB` of the loop estimates
(`Induction/Defs.lean:68`); the factor `W` in `(K + W)` is the block unit. -/
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

/-- `(N η)⁻¹ ≤ 𝓑_{η,K}` for `η > 0`, `K ≥ 0`: the floor of the control (absorbs the additive `W^{-D}` of
`(Eq:Gdecay)` and the net error). -/
theorem inv_size_mul_le_calB (hd : 2 ≤ d) {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) :
    (((sz.size n : ℕ) : ℝ) * η)⁻¹ ≤ calB sz n η K := by
  have hW := W_pos_real sz n
  have hlam : 0 < sz.lam n ^ 2 + η := by positivity
  unfold calB
  have : 0 ≤ (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) := by
    have : 0 ≤ K + ((sz.W n : ℕ) : ℝ) := by linarith
    positivity
  linarith

/-- `𝓑_{η,K}` is nonincreasing in the distance `K ≥ 0`. -/
theorem calB_antitone (hd : 2 ≤ d) {η K K' : ℝ} (hη : 0 < η) (hK : 0 ≤ K) (hKK : K ≤ K') :
    calB sz n η K' ≤ calB sz n η K := by
  have hW := W_pos_real sz n
  have hlam : 0 < sz.lam n ^ 2 + η := by positivity
  unfold calB
  have h1 : 0 < K + ((sz.W n : ℕ) : ℝ) := by linarith
  have h2 : (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) ≤ (K' + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) :=
    pow_le_pow_left₀ h1.le (by linarith) _
  have h3 : 0 < ((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) := by positivity
  have h4 : ((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) ≤
      ((sz.W n : ℕ) : ℝ) ^ 2 * (K' + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have : (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K' + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) ≤
      (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) :=
    div_le_div_of_nonneg_left (by positivity) h3 h4
  linarith

theorem calB_nonneg {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) : 0 ≤ calB sz n η K := by
  have hW := W_pos_real sz n
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : 0 < K + ((sz.W n : ℕ) : ℝ) := by linarith
  unfold calB
  positivity

/-- **The `L^∞`/`ℓ¹` conversion of the distance in `𝓑_{η,K}`** (T2001e, `1_2:274`; preflight row 4): if
`0 ≤ K ≤ K' ≤ d K` then `d^{-(d-2)} 𝓑_{η,K} ≤ 𝓑_{η,K'} ≤ 𝓑_{η,K}` (`K' + W ≤ d (K + W)`; the second term of `𝓑` does not
depend on `K`). -/
theorem calB_dist_compare (hd : 2 ≤ d) {η K K' : ℝ} (hη : 0 < η) (hK : 0 ≤ K) (hKK : K ≤ K')
    (hKd : K' ≤ (d : ℝ) * K) :
    (((d : ℝ) ^ (d - 2))⁻¹) * calB sz n η K ≤ calB sz n η K' ∧ calB sz n η K' ≤ calB sz n η K := by
  refine ⟨?_, calB_antitone sz n hd hη hK hKK⟩
  have hW := W_pos_real sz n
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hlam : 0 < sz.lam n ^ 2 + η := by positivity
  have hK1 : 0 < K + ((sz.W n : ℕ) : ℝ) := by linarith
  have hK2 : 0 < K' + ((sz.W n : ℕ) : ℝ) := by linarith
  have hdd : 0 < (d : ℝ) ^ (d - 2) := by positivity
  have hdd1 : 1 ≤ (d : ℝ) ^ (d - 2) := one_le_pow₀ hd1
  have h3 : K' + ((sz.W n : ℕ) : ℝ) ≤ (d : ℝ) * (K + ((sz.W n : ℕ) : ℝ)) := by nlinarith
  have h4 : (K' + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) ≤ (d : ℝ) ^ (d - 2) * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hK2.le h3 _
  have hc : 0 < ((sz.W n : ℕ) : ℝ) ^ 2 * (K' + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) := by positivity
  have hcb : ((sz.W n : ℕ) : ℝ) ^ 2 * (K' + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) ≤
      ((sz.W n : ℕ) : ℝ) ^ 2 * ((d : ℝ) ^ (d - 2) * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have hT : ((d : ℝ) ^ (d - 2))⁻¹ *
        ((sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2))) ≤
      (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K' + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) := by
    have e : ((d : ℝ) ^ (d - 2))⁻¹ *
        ((sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2))) =
        (sz.lam n ^ 2 + η)⁻¹ /
          (((sz.W n : ℕ) : ℝ) ^ 2 * ((d : ℝ) ^ (d - 2) * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2))) := by
      have h5 : (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2) ≠ 0 := by positivity
      have h6 : ((sz.W n : ℕ) : ℝ) ≠ 0 := hW.ne'
      have h7 : (d : ℝ) ^ (d - 2) ≠ 0 := hdd.ne'
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) hc hcb
  have hB : 0 ≤ (((sz.size n : ℕ) : ℝ) * η)⁻¹ := by
    have : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  have hB' : ((d : ℝ) ^ (d - 2))⁻¹ * (((sz.size n : ℕ) : ℝ) * η)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * η)⁻¹ :=
    mul_le_of_le_one_left hB (inv_le_one_of_one_le₀ hdd1)
  unfold calB
  rw [mul_add]
  exact add_le_add hT hB'

/-- **The conversion at the freeze**: `distB` is `W |a-b|_∞` (merged `zdistInf`, as `STLocalEntry`); the BA endpoints of
T2161 keep the `ℓ¹` block distance `W |a-b|_1` (`zdistD`).  The merged `zdistInf_le_zdistD`, `zdistD_le_mul_zdistInf`
(`Defs/Sizes.lean`) give `K ≤ K' ≤ d K`, so the two thresholds differ by at most `d^{d-2}`, which `W^τ` absorbs. -/
theorem calB_distB_compare (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (a b : Zd d (sz.L n)) :
    (((d : ℝ) ^ (d - 2))⁻¹) * calB sz n η (distB sz n a b) ≤
        calB sz n η (((sz.W n : ℕ) : ℝ) * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)) ∧
      calB sz n η (((sz.W n : ℕ) : ℝ) * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)) ≤ calB sz n η (distB sz n a b) := by
  have hW := W_pos_real sz n
  have h1 : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤ ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d (sz.L n) (a - b)
  have h2 : ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ) ≤ (d : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := by
    exact_mod_cast zdistD_le_mul_zdistInf d (sz.L n) (a - b)
  refine calB_dist_compare sz n hd hη (by unfold distB; positivity) ?_ ?_
  · unfold distB
    exact mul_le_mul_of_nonneg_left h1 hW.le
  · unfold distB
    calc ((sz.W n : ℕ) : ℝ) * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)
        ≤ ((sz.W n : ℕ) : ℝ) * ((d : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 hW.le
      _ = (d : ℝ) * (((sz.W n : ℕ) : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) := by ring

end Scalars


/-! ## 3. The form decision: the explicit `W^τ`, `N^{-D}` form against the merged `Prec` (compiled bridge) -/

section Form

variable {d : ℕ} (sz : Sizes d)

/-- **`StochDomAt` ⟹ explicit, for any law** (the bridge BA-M1/M2 and MA-03 need): from `≺` at the scale `N^τ` (union
inside) for an arbitrary probability space `(Ω, P)`, and `W ≥ N^𝔠` (`Bandwidth`), the paper's `W^τ` form with `N^{-D}`:
`N^{𝔠τ} ≤ W^τ` (`size_rpow_le_W_rpow`).  Needs `ζ ≥ 0` (the controls are `≥ 0`) and no `N → ∞`.  The block Anderson
law is `seqP (sz.withLam 0)` (T2173a), so the lemma is stated for every `P`. -/
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

/-- **Explicit ⟹ `Prec`**: `W^{dτ} ≤ N^τ` (`W_rpow_le`), so the explicit form at `d τ` gives `Prec` at `τ`.  Needs
no `Bandwidth`: the two forms are equivalent for admissible `sz`. -/
theorem prec_of_explicit (hd : 0 < d) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (h : ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))) :
    sz.Prec ξ ζ := by
  intro τ hτ D hD
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  filter_upwards [h ((d : ℝ) * τ) D (by positivity) hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨u, hu⟩
  refine ⟨u, lt_of_le_of_lt ?_ hu⟩
  have h1 := Sizes.W_rpow_le sz hd n (τ := (d : ℝ) * τ) (by positivity)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ ((d : ℝ) * τ / d) = ((sz.size n : ℕ) : ℝ) ^ τ := by
    congr 1; field_simp
  rw [h2] at h1
  exact mul_le_mul_of_nonneg_right h1 (hζ n u ω)

/-- **Sections ⟹ eventually for all** (the diagonal argument that turns `UNMLOut`, which is stated along
sequences `z : ℕ → ℂ`, into a statement with `N₀` uniform over `𝐃_{κ,ε}`).  Port of RBM2D
`EndpointsFromSTO_eventually_forall_of_sections` (`RBM2D/Main/EndpointsFromSTO.lean:35`, commit `c9a24cf`;
RBM1D `eventually_forall_of_forall_sequences`, `RBM1D/Flow/EventuallyUniformBySequences.lean:25`, commit `d6add37`), proof verbatim. -/
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

/-- **A deterministic `Prec` is a deterministic bound** (the expectation half `(Meq:QdS1)`, `(Meq:QdS2)`: the left
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
for `κ > 2` or `ε > 1` (and `N > 1`) it is empty (lesson 25). -/
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


/-! ## 5. The interface bridges to UN (`locSC → UNLocAvgBand`, `QUE → UNQueBand`) -/

section Bridges

/-- **`locSC → UNLocAvgBand`**: the second half of `locSC` (`(G_bound_ave)`, `∩_z` inside) is the merged UN pin; the only
rewriting is `𝓑_{η,0} = sz.Bctl n (1 - η)` under the binder (`calB_zero_eq_Bctl`, `0 < Im z` from `locDomain`), because the
pin keeps the paper's `𝓑`. -/
theorem locSC_to_UNLocAvgBand : locSC → UNLocAvgBand := by
  intro h d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD
  filter_upwards [(h d hd 𝔠 𝔡 sz hA κ ε τ D hκ hε hτ hD)] with n hn
  refine le_trans (measure_mono ?_) hn.2
  rintro ω ⟨z, hz, a, ha⟩
  refine ⟨z, hz, a, ?_⟩
  rw [calB_zero_eq_Bctl sz n (by omega) (locDomain_im_pos hz)]
  exact ha

/-- **`QUE → UNQueBand`**: the first half of `(Meq:QUE)`, a projection (the events and the bound are the merged
`queBadMat`, `queBound`). -/
theorem QUE_to_UNQueBand : QUE → UNQueBand := by
  intro h d hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6
  exact (h d hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6).mono fun n hn E hE a => (hn E hE).1 a

end Bridges


/-! ## 7. Compiled nonempty instances at `d = 3` on `SizesInst.sz0` and extreme inputs (CLAUDE.md §4 step 2)

Data: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`,
`N = 2097152`), `(𝔠, 𝔡) = (1/6, 1/10)`, `κ = 1/10`; `locSC`, `QDiff`: `ε = 1/20`, `τ = 1/10`, `D = 2`; `decol`: `τ = 1/10`, `D = 1`;
`QUE`: `ε₀ = 1/30`, `c = 1/60`, `τ = 1/10` (`0 < ε₀ < 𝔡/2 = 1/20`, `0 < c < ε₀ ∧ 𝔡/5 = 1/50`).  The endpoints are pins that
other gates prove: each instance applies the endpoint (a hypothesis of the example) with every deterministic hypothesis
(`3 ≤ d`, `Admissible`, the positivity of the constants and the ranges of `ε₀, c`) discharged. -/

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- The point `z = 1/2 + i N^{-4/5}` of `𝐃_{1/10,1/10}` at `n = 0` (merged `sz0_locDomain`). -/
def zI : ℂ := ⟨1 / 2, ((sz0.size 0 : ℕ) : ℝ) ^ (-(4 / 5) : ℝ)⟩

theorem zI_dom : sz0.locDomain (1 / 10) (1 / 10) 0 zI := sz0_locDomain

theorem zI_im_pos : 0 < zI.im := locDomain_im_pos zI_dom

theorem zI_im_le : zI.im ≤ 1 := zI_dom.2.2

theorem zI_re_le : |zI.re| ≤ 2 - 1 / 10 := zI_dom.1

/-- **`decol` (Thm 2.1)** at the instance. -/
theorem inst_decol (h : decol) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)

/-- **`locSC` (Thm 2.2)** at the instance. -/
theorem inst_locSC (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) :=
  h 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- **`QUE` (Thm 2.3)** at the instance: `ε₀ = 1/30`, `c = 1/60`, `τ = 1/10`. -/
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

/-- **`QDiff` (Thm 2.5)** at the instance (the probability half and the expectation half). -/
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

/-- **`BUniv` (Thm 2.4)** at the instance (the merged `UNBUniv`): `k = 1`, `E = 0`, `𝒪 = bump`. -/
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


/-! ### The `(eq:WO)` edges: `ilambda = W^{-d/2+𝔡}` and `ilambda = 𝔡⁻¹` -/

/-- Blocks `L_n = n + 3`, sides `W_n = (n+2)^6`, `(𝔠, 𝔡) = (1/4, 1/5)`: `W ≥ N^{1/4}`; the coupling is set by `withLam`. -/
def szE : Sizes 3 where
  L := fun n => n + 3
  W := fun n => (n + 2) ^ 6
  lam := fun _ => 1
  three_le_L := fun n => by omega
  W_pos := fun n => by positivity

/-- The lower edge of `(eq:WO)`: `ilambda_n = W_n^{-d/2+𝔡}` (`𝔡 = 1/5`, `ilambda → 0`). -/
def szLo : Sizes 3 := szE.withLam fun n => ((szE.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 5)

/-- The upper edge of `(eq:WO)`: `ilambda_n = 𝔡⁻¹ = 5` (`ilambda > 1`, the footnote `1_2:372` regime). -/
def szUp : Sizes 3 := szE.withLam fun _ => 5

theorem szE_size_le (n : ℕ) : szE.size n ≤ (szE.W n) ^ 4 := by
  have h : (n + 3) ^ 3 ≤ (n + 2) ^ 6 := by
    have h1 : n + 3 ≤ (n + 2) ^ 2 := by nlinarith
    calc (n + 3) ^ 3 ≤ ((n + 2) ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = (n + 2) ^ 6 := by ring
  calc szE.size n = ((n + 2) ^ 6 * (n + 3)) ^ 3 := rfl
    _ = (n + 2) ^ 18 * (n + 3) ^ 3 := by ring
    _ ≤ (n + 2) ^ 18 * (n + 2) ^ 6 := Nat.mul_le_mul_left _ h
    _ = ((n + 2) ^ 6) ^ 4 := by ring

theorem szE_bandwidth : szE.Bandwidth (1 / 4) := by
  refine Eventually.of_forall fun n => ?_
  have h : ((szE.size n : ℕ) : ℝ) ≤ ((szE.W n : ℕ) : ℝ) ^ 4 := by exact_mod_cast szE_size_le n
  calc ((szE.size n : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ (((szE.W n : ℕ) : ℝ) ^ 4) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) h (by norm_num)
    _ = (szE.W n : ℝ) := by
        rw [show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)

theorem szE_tendsto : szE.SizeTendsto := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  have h1 : n + 3 ≤ (n + 2) ^ 6 * (n + 3) := Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : (n + 2) ^ 6 * (n + 3) ≤ ((n + 2) ^ 6 * (n + 3)) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h3 : n ≤ szE.size n := by
    change n ≤ ((n + 2) ^ 6 * (n + 3)) ^ 3
    omega
  exact_mod_cast h3

theorem szLo_admissible : szLo.Admissible (1 / 4) (1 / 5) := by
  refine ⟨by norm_num, by norm_num, szE_tendsto, szE_bandwidth, Eventually.of_forall fun n => ⟨le_rfl, ?_⟩⟩
  have hW : (1 : ℝ) ≤ ((szLo.W n : ℕ) : ℝ) := by exact_mod_cast szLo.W_pos n
  have h1 : ((szLo.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 5) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW (by norm_num)
  change ((szE.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 5) ≤ (1 / 5 : ℝ)⁻¹
  have hW' : (1 : ℝ) ≤ ((szE.W n : ℕ) : ℝ) := hW
  refine (Real.rpow_le_one_of_one_le_of_nonpos hW' (by norm_num)).trans (by norm_num)

theorem szUp_admissible : szUp.Admissible (1 / 4) (1 / 5) := by
  refine ⟨by norm_num, by norm_num, szE_tendsto, szE_bandwidth, Eventually.of_forall fun n => ⟨?_, by norm_num [szUp, Sizes.withLam]⟩⟩
  have hW : (1 : ℝ) ≤ ((szE.W n : ℕ) : ℝ) := by exact_mod_cast szE.W_pos n
  have h1 : ((szE.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 5) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW (by norm_num)
  exact h1.trans (by norm_num [szUp, Sizes.withLam])

/-- `locSC` at the lower edge `ilambda = W^{-d/2+𝔡}` (`𝔠 = 1/4`, `𝔡 = 1/5`, `ilambda → 0`). -/
theorem inst_locSC_lo (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP szLo {ω | locBad1 szLo (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz szLo n ^ (-(2 : ℝ))) ∧
      Sizes.seqP szLo {ω | locBad2 szLo (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz szLo n ^ (-(2 : ℝ))) :=
  h 3 le_rfl (1 / 4) (1 / 5) szLo szLo_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `locSC` at the upper edge `ilambda = 𝔡⁻¹ = 5` (`ilambda > 1`). -/
theorem inst_locSC_up (h : locSC) :
    ∀ᶠ n in atTop, Sizes.seqP szUp {ω | locBad1 szUp (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz szUp n ^ (-(2 : ℝ))) ∧
      Sizes.seqP szUp {ω | locBad2 szUp (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz szUp n ^ (-(2 : ℝ))) :=
  h 3 le_rfl (1 / 4) (1 / 5) szUp szUp_admissible (1 / 10) (1 / 20) (1 / 10) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

/-- `QUE` at the upper edge (`ilambda = 5`): `ε₀ = 1/20·(2/3)`, `c = ε₀/2` inside `(0, 𝔡/2) = (0, 1/10)` and
`(0, ε₀ ∧ 𝔡/5 = 1/25)`. -/
theorem inst_QUE_up (h : QUE) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
      ∀ a : Zd 3 (szUp.L n),
        Sizes.seqP szUp {ω | queBadMat 3 (szUp.L n) (szUp.W n) (szUp.lam n) (1 / 15) (1 / 30) E a (szUp.seqXmat n ω)} ≤
          queBound (szUp.W n) (1 / 5) (1 / 15) (1 / 30) (1 / 10) := by
  filter_upwards [h 3 le_rfl (1 / 4) (1 / 5) szUp szUp_admissible (1 / 10) (by norm_num) (1 / 15) (1 / 30) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)] with n hn E hE a
  exact (hn E hE).1 a


/-! ### Extreme inputs (TEAM §8 lesson 25) -/

/-- `κ = 2`, `ε = 1`: `𝐃_{2,1}` is the single point `i` (nonempty); the empty domain starts at `κ > 2` or `ε > 1`
(`locDomain_empty_kappa`, `locDomain_empty_eps`): the ticket's "`κ ≥ 2`, `ε ≥ 1`" is off at equality. -/
theorem domain_extreme : sz0.locDomain 2 1 0 Complex.I ∧ ¬ sz0.locDomain 3 (1 / 20) 0 zI ∧
    ¬ sz0.locDomain (1 / 10) 2 0 zI := by
  refine ⟨⟨by simp, by simp, by simp⟩, locDomain_empty_kappa sz0 (by norm_num) 0 zI,
    locDomain_empty_eps sz0 (by norm_num) ?_ zI⟩
  have : (1 : ℝ) < Nsz sz0 0 := by
    have h := sz0_values.2.2.1
    simp only [Nsz, h]; norm_num
  exact this

/-- Over the empty domain (`κ = 3`) the failure event of `(G_bound)` is empty, so the endpoint is vacuous there: the pins are
tried with a domain that has no points. -/
theorem locBad1_empty_kappa (n : ℕ) (ω : sz0.SeqΩ) : ¬ locBad1 sz0 3 (1 / 20) (1 / 10) n ω :=
  fun ⟨z, hz, _⟩ => locDomain_empty_kappa sz0 (by norm_num) n z hz

/-- The window edge `E = ±(2-κ)`: `Im m(E) = √(κ(4-κ))/2` (the constant `κ'` of `thetaDiff` is attained). -/
theorem im_mE_edge {κ : ℝ} : (mE (2 - κ)).im = Real.sqrt (κ * (4 - κ)) / 2 ∧
    (mE (-(2 - κ))).im = Real.sqrt (κ * (4 - κ)) / 2 := by
  refine ⟨?_, ?_⟩ <;> rw [mE_im] <;> congr 2 <;> ring


/-- `(Meq:QUE2)` with `A = univ`: the failure event is empty (`∑_a ∑_{x∈[a]} |ψ_k(x)|² = 1 = W^d |univ|/N`, so the
left side is `0 < W^{d-c}|univ|/N`). -/
theorem que2BadMat_univ {d L W : ℕ} [NeZero L] [NeZero W] (lam ε₀ c E : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ¬ que2BadMat d L W lam ε₀ c E Finset.univ M := by
  rintro ⟨μ, ψ, hψ, k, -, hk⟩
  have hsum : ∀ f : Idx d L W → ℝ, ∑ a : Zd d L, ∑ x ∈ Iblk d L W a, f x = ∑ x, f x := by
    intro f
    simp only [Iblk, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  have h1 : ∑ x, ‖ψ k x‖ ^ 2 = 1 := by
    have h := hψ.1 k k
    simp only [dotProduct, Pi.star_apply, ite_true] at h
    have h2 : ((∑ x, ‖ψ k x‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]; push_cast
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.star_def, Complex.conj_mul']
    exact_mod_cast h2
  have hcard : ((Finset.univ : Finset (Zd d L)).card : ℝ) = (L : ℝ) ^ d := by
    rw [Finset.card_univ, card_Zd]; push_cast; rfl
  have hN : (((W * L) ^ d : ℕ) : ℝ) = (W : ℝ) ^ d * (L : ℝ) ^ d := by push_cast; ring
  have hWp : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  rw [hsum (fun x => ‖ψ k x‖ ^ 2), h1, hcard, hN] at hk
  have hz : (W : ℝ) ^ d / ((W : ℝ) ^ d * (L : ℝ) ^ d) * (L : ℝ) ^ d = 1 := by field_simp
  rw [hz, sub_self, abs_zero] at hk
  have hpos : 0 < (W : ℝ) ^ ((d : ℝ) - c) * (L : ℝ) ^ d / ((W : ℝ) ^ d * (L : ℝ) ^ d) := by positivity
  linarith

/-- `(Meq:QUE2)` with `A = ∅` is the event that the window contains an eigenvalue (the inequality `0 ≤ 0` holds): for the zero
matrix and `E = 0` it is nonempty, so the bound fails; this is why `A ≠ ∅` is part of the statement (T2001f). -/
theorem que2BadMat_empty_zero {d L W : ℕ} [NeZero L] [NeZero W] (lam ε₀ c : ℝ) (hW : (1 : ℝ) ≤ W) (hlam : 0 ≤ lam) :
    que2BadMat d L W lam ε₀ c 0 ∅ (0 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
  refine ⟨fun _ => 0, fun k => Pi.single k 1, isOrthoEigenbasis_zero, 0, ?_, ?_⟩
  · unfold queWindow
    have hWp : (0 : ℝ) < (W : ℝ) := by linarith
    have : 0 ≤ (W : ℝ) ^ (-ε₀) * (lam * (W : ℝ) ^ ((d : ℝ) / 2) / (((W * L) ^ d : ℕ) : ℝ)) := by positivity
    simpa using this
  · simp


/-- `𝓑_{η,0} = Bctl n (1 - η)` and the floor `(Nη)⁻¹ ≤ 𝓑` at `n = 0`, `η = 1/2`. -/
theorem inst_calB :
    calB sz0 0 (1 / 2) 0 = sz0.Bctl 0 (1 - 1 / 2) ∧
      (((sz0.size 0 : ℕ) : ℝ) * (1 / 2))⁻¹ ≤ calB sz0 0 (1 / 2) 0 :=
  ⟨calB_zero_eq_Bctl sz0 0 (by norm_num) (by norm_num),
    inv_size_mul_le_calB sz0 0 (by norm_num) (by norm_num) le_rfl⟩

/-- The `L^∞`/`ℓ¹` conversion at `n = 0`, `η = 1/2` and every pair of blocks of `Z_4^3`: the factor is `3^{-1}`
(`d^{-(d-2)}` at `d = 3`). -/
theorem inst_distB_compare (a b : Zd 3 (sz0.L 0)) :
    (((3 : ℕ) : ℝ) ^ (3 - 2))⁻¹ * calB sz0 0 (1 / 2) (distB sz0 0 a b) ≤
        calB sz0 0 (1 / 2) (((sz0.W 0 : ℕ) : ℝ) * ((zdistD 3 (sz0.L 0) (a - b) : ℕ) : ℝ)) ∧
      calB sz0 0 (1 / 2) (((sz0.W 0 : ℕ) : ℝ) * ((zdistD 3 (sz0.L 0) (a - b) : ℕ) : ℝ)) ≤
        calB sz0 0 (1 / 2) (distB sz0 0 a b) :=
  calB_distB_compare sz0 0 (by norm_num) (by norm_num) a b


end Inst

end RBM.Endpoints
