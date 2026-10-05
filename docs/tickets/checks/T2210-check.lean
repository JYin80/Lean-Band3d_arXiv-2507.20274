/-
Release check for T2210 (dispatcher V1, Mon Oct  5 19:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §10, §16, §17, §20,
§29, §45 O2, §57 (1), §68 (10)).
MA-01 (main-theorem assembly, gate MA; first proof ticket of the MA split, T2192 portmap P.5): the endpoint freeze
`RBM3D/Endpoints.lean`, moved verbatim from the T2192 probe (`git show 97d958e:RBM3D/Probe/T2192Pins.lean`, branch
`t/T2192`; design merged report-only at 3429d7d): vocabulary, the four band endpoints `decol`, `locSC`, `QUE`, `QDiff`
(Thm 2.1, 2.2, 2.3, 2.5) in the explicit form `W^τ`, `N^{-D}` (D504), `BUniv := UNBUniv` (Thm 2.4), the `𝓑` lemmas,
the form bridges `Prec ↔ explicit`, the domain lemmas, the UN bridges, and the instances of the MA-01 part.
Section 1: the merged names the moved text uses (exact namespaces; file and last commit on `main` cda3bb2).
Section 2: the vocabulary of probe §1 (`:48-210`), docstrings stripped, in the temporary namespace
`RBM.Endpoints.T2210Check`; the five endpoint pins as `decol_pin`, `locSC_pin`, `QUE_pin`, `QDiff_pin` (probe text
verbatim) and `BUniv_pin` (the probe's `abbrev BUniv : Prop := UNBUniv`).  T2210 defines each in `RBM.Endpoints` under
the probe's name (`decol`, …, `abbrev BUniv`), docstrings kept.
Section 3: the statements of the theorems T2210 moves, as `Prop`-valued `example`s (no proof obligation; the probe's
binders and types verbatim, the only change `decol`/`locSC`/`QUE`/`QDiff`/`BUniv` ↦ `*_pin`), and the instance point
`zI`.  Omitted: the private helpers `W_pos_real`, `L_pos_real`, `size_cast`, and the `(eq:WO)`-edge data `szE`, `szLo`,
`szUp` with their eight theorems (`szE` is a structure value with tactic proofs in its fields); the verbatim criterion
of the ticket covers them.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Imports: `RBM3D.Universality.Pins` only (its import closure contains every module of section 1 and is unchanged
between the probe's base 76b840e and `main` cda3bb2); not the probe, not `RBM3D`.
Run from the main worktree: `lake env lean docs/tickets/checks/T2210-check.lean`.
-/
import RBM3D.Universality.Pins

/-! ## 1. Merged names -/

-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.L
#check @RBM.Gauss.Sizes.W
#check @RBM.Gauss.Sizes.lam
#check @RBM.Gauss.Sizes.three_le_L
#check @RBM.Gauss.Sizes.W_pos
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.W_rpow_le
#check @RBM.Gauss.Sizes.size_rpow_le_W_rpow
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.zdistD_le_mul_zdistInf
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.SizesInst.sz0_admissible
#check @RBM.Gauss.SizesInst.sz0_locDomain
-- `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.card_Zd
-- `RBM3D/Defs/Params.lean` (c3f3d5d)
#check @RBM.Bparam
-- `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.msc
#check @RBM.mE
#check @RBM.mE_im
-- `RBM3D/Propagator/Basic.lean` (020ec7a)
#check @RBM.Theta
-- `RBM3D/Defs/StochDomAt.lean` (9e2b00f)
#check @RBM.badSetAt
#check @RBM.StochDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.one_le_size
-- `RBM3D/Gauss/FineModel.lean` (0a873f1)
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqXmat_isHermitian
#check @RBM.Gauss.Xmat_isHermitian
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.Gn
-- `RBM3D/Induction/Defs.lean` (64bdfd3)
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STblk
-- `RBM3D/Universality/Pins.lean` (f8ad4b4)
#check @RBM.Univ.Nsz
#check @RBM.Univ.IsOrthoEigenbasis
#check @RBM.Univ.queWindow
#check @RBM.Univ.queBadMat
#check @RBM.Univ.queBound
#check @RBM.Univ.kPoint
#check @RBM.Univ.gueP
#check @RBM.Univ.UNBUniv
#check @RBM.Univ.UNQueBand
#check @RBM.Univ.UNLocAvgBand
#check @RBM.Univ.un_bUniv_of_rows
#check @RBM.Univ.UNInst.bump
#check @RBM.Univ.UNInst.bump_testFun
#check @RBM.Univ.UNInst.isOrthoEigenbasis_zero

/-! ## 2. Vocabulary and endpoint pins (probe §1 `:48-210`; docstrings stripped) -/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints.T2210Check

section Endpoints

variable {d : ℕ}

-- probe `:57`
def calB (sz : Sizes d) (n : ℕ) (η K : ℝ) : ℝ :=
  (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) +
    (((sz.size n : ℕ) : ℝ) * η)⁻¹

-- probe `:66`
def distB (sz : Sizes d) (n : ℕ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)

-- probe `:70`
def Mband (sz : Sizes d) (n : ℕ) (z : ℂ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if x = y then msc z else 0

-- probe `:74`
def avg2 (sz : Sizes d) (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (a b : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y

-- probe `:79`
def ThetaPM (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ)

-- probe `:83`
def ThetaPP (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (msc z ^ 2)

-- probe `:87`
def profPM (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * ThetaPM sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d

-- probe `:91`
def profPP (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  msc z ^ 2 * ThetaPP sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d

-- probe `:95`
def qdBound (sz : Sizes d) (n : ℕ) (τ η : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b))
    (calB sz n η 0 ^ 2)

-- probe `:100`
def qdBoundExp (sz : Sizes d) (n : ℕ) (τ η : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n η 0 ^ 2 *
    ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 : ℝ) / 5) + calB sz n η 0)

-- probe `:106`
def decolBad (sz : Sizes d) (n : ℕ) (κ τ : ℝ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqXmat n ω) μ ψ → ∀ k, |μ k| ≤ 2 - κ → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)

-- probe `:113`
def locBad1z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n),
    ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
      ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2

-- probe `:119`
def locBad2z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z‖

-- probe `:124`
def qd1Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n z a b‖

-- probe `:129`
def qd2Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b - profPP sz n z a b‖

-- probe `:135`
def locBad1 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad1z sz τ n z ω

-- probe `:139`
def locBad2 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad2z sz τ n z ω

-- probe `:143`
def qd1Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd1Badz sz τ n z ω

-- probe `:147`
def qd2Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd2Badz sz τ n z ω

-- probe `:153`
def que2BadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (A : Finset (Zd d L))
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ k, queWindow d L W lam ε₀ E (μ k) ∧
      (W : ℝ) ^ ((d : ℝ) - c) * (A.card : ℝ) / (((W * L) ^ d : ℕ) : ℝ) ≤
        |(∑ a ∈ A, ∑ x ∈ Iblk d L W a, ‖ψ k x‖ ^ 2) -
            (W : ℝ) ^ d / (((W * L) ^ d : ℕ) : ℝ) * (A.card : ℝ)|

-- probe `:164` (`decol`)
def decol_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | decolBad sz n κ τ ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

-- probe `:171` (`locSC`)
def locSC_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))

-- probe `:181` (`QUE`)
def QUE_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
        (∀ a : Zd d (sz.L n),
          Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ) ∧
        (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
          Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
            queBound (sz.W n) 𝔡 ε₀ c τ)

-- probe `:196` (`QDiff`)
def QDiff_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      (Sizes.seqP sz {ω | qd1Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
       Sizes.seqP sz {ω | qd2Bad sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, sz.locDomain κ ε n z → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
            profPM sz n z a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
            profPP sz n z a b‖ ≤ qdBoundExp sz n τ z.im

-- probe `:208` (`abbrev BUniv : Prop := UNBUniv`)
def BUniv_pin : Prop := UNBUniv

end Endpoints

/-! ## 3. Statements of the theorems T2210 moves (`Prop`-valued `example`s, no proof obligation; the probe's binders and
types verbatim, the only change `decol`/`locSC`/`QUE`/`QDiff`/`BUniv` ↦ `*_pin`) -/

section Scalars

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

-- statement of `calB_zero_eq_Bctl` (probe `:230`)
example (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) : Prop :=
    calB sz n η 0 = sz.Bctl n (1 - η)

-- statement of `calB_blk_eq_STWB` (probe `:245`)
example (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (k : ℕ) : Prop :=
    calB sz n η (((sz.W n : ℕ) : ℝ) * (k : ℝ)) = STWB sz n (1 - η) k

-- statement of `inv_size_mul_le_calB` (probe `:263`)
example (hd : 2 ≤ d) {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) : Prop :=
    (((sz.size n : ℕ) : ℝ) * η)⁻¹ ≤ calB sz n η K

-- statement of `calB_antitone` (probe `:274`)
example (hd : 2 ≤ d) {η K K' : ℝ} (hη : 0 < η) (hK : 0 ≤ K) (hKK : K ≤ K') : Prop :=
    calB sz n η K' ≤ calB sz n η K

-- statement of `calB_nonneg` (probe `:291`)
example {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) : Prop :=
  0 ≤ calB sz n η K

-- statement of `calB_dist_compare` (probe `:301`)
example (hd : 2 ≤ d) {η K K' : ℝ} (hη : 0 < η) (hK : 0 ≤ K) (hKK : K ≤ K')
    (hKd : K' ≤ (d : ℝ) * K) : Prop :=
    (((d : ℝ) ^ (d - 2))⁻¹) * calB sz n η K ≤ calB sz n η K' ∧ calB sz n η K' ≤ calB sz n η K

-- statement of `calB_distB_compare` (probe `:344`)
example (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (a b : Zd d (sz.L n)) : Prop :=
    (((d : ℝ) ^ (d - 2))⁻¹) * calB sz n η (distB sz n a b) ≤
        calB sz n η (((sz.W n : ℕ) : ℝ) * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)) ∧
      calB sz n η (((sz.W n : ℕ) : ℝ) * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)) ≤ calB sz n η (distB sz n a b)

end Scalars

section Form

variable {d : ℕ} (sz : Sizes d)

-- statement of `explicit_of_stochDomAt` (probe `:375`)
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → Ω → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hb : sz.Bandwidth 𝔠) (h : StochDomAt P sz.size ξ ζ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) : Prop :=
    ∀ᶠ n in atTop, P {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

-- statement of `explicit_of_prec` (probe `:391`)
example {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hb : sz.Bandwidth 𝔠) (h : sz.Prec ξ ζ) {τ D : ℝ} (hτ : 0 < τ)
    (hD : 0 < D) : Prop :=
    ∀ᶠ n in atTop, Sizes.seqP sz {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

-- statement of `prec_of_explicit` (probe `:400`)
example (hd : 0 < d) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (h : ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | ∃ u, ((sz.W n : ℕ) : ℝ) ^ τ * ζ n u ω < ξ n u ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))) : Prop :=
    sz.Prec ξ ζ

-- statement of `eventually_forall_of_sections` (probe `:422`)
example {Z : ℕ → Type*} (hne : ∀ n, Nonempty (Z n))
    {Q : ∀ n, Z n → Prop} (h : ∀ s : ∀ n, Z n, ∀ᶠ n in atTop, Q n (s n)) : Prop :=
    ∀ᶠ n in atTop, ∀ z : Z n, Q n z

-- statement of `det_of_prec` (probe `:442`)
example (hsz : sz.SizeTendsto) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hξ : ∀ n u ω ω', ξ n u ω = ξ n u ω') (hζ : ∀ n u ω ω', ζ n u ω = ζ n u ω')
    (h : sz.Prec ξ ζ) {τ : ℝ} (hτ : 0 < τ) : Prop :=
    ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω

end Form

section Domain

variable {d : ℕ}

-- statement of `STWB_nonneg` (probe `:1094`)
example (sz : Sizes d) (n : ℕ) (u : ℝ) (k : ℕ) : Prop :=
  0 ≤ STWB sz n u k

-- statement of `Nsz_pos` (probe `:1098`)
example (sz : Sizes d) (n : ℕ) : Prop :=
  (0 : ℝ) < Nsz sz n

-- statement of `locDomain_im_pos` (probe `:1103`)
example {sz : Sizes d} {κ ε : ℝ} {n : ℕ} {z : ℂ} (h : sz.locDomain κ ε n z) : Prop :=
  0 < z.im

-- statement of `locDomain_nonempty` (probe `:1108`)
example (sz : Sizes d) {κ ε : ℝ} (hκ : κ ≤ 2) (hε : ε ≤ 1) (n : ℕ) : Prop :=
    ∃ z : ℂ, sz.locDomain κ ε n z

-- statement of `locDomain_empty_kappa` (probe `:1116`)
example (sz : Sizes d) {κ ε : ℝ} (hκ : 2 < κ) (n : ℕ) (z : ℂ) : Prop :=
    ¬ sz.locDomain κ ε n z

-- statement of `locDomain_empty_eps` (probe `:1123`)
example (sz : Sizes d) {κ ε : ℝ} (hε : 1 < ε) {n : ℕ} (hN : 1 < Nsz sz n) (z : ℂ) : Prop :=
    ¬ sz.locDomain κ ε n z

end Domain

section Bridges

-- statement of `locSC_to_UNLocAvgBand` (probe `:2055`)
example : Prop :=
  locSC_pin → UNLocAvgBand

-- statement of `QUE_to_UNQueBand` (probe `:2066`)
example : Prop :=
  QUE_pin → UNQueBand

end Bridges

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

-- probe `:2117`
def zI : ℂ := ⟨1 / 2, ((sz0.size 0 : ℕ) : ℝ) ^ (-(4 / 5) : ℝ)⟩

-- statement of `zI_dom` (probe `:2119`)
example : Prop :=
  sz0.locDomain (1 / 10) (1 / 10) 0 zI

-- statement of `zI_im_pos` (probe `:2121`)
example : Prop :=
  0 < zI.im

-- statement of `zI_im_le` (probe `:2123`)
example : Prop :=
  zI.im ≤ 1

-- statement of `zI_re_le` (probe `:2125`)
example : Prop :=
  |zI.re| ≤ 2 - 1 / 10

-- statement of `inst_decol` (probe `:2128`)
example (h : decol_pin) : Prop :=
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | decolBad sz0 n (1 / 10) (1 / 10) ω} ≤
      ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))

-- statement of `inst_locSC` (probe `:2134`)
example (h : locSC_pin) : Prop :=
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | locBad1 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
      Sizes.seqP sz0 {ω | locBad2 sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))

-- statement of `inst_QUE` (probe `:2142`)
example (h : QUE_pin) : Prop :=
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
      (∀ a : Zd 3 (sz0.L n),
        Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) ∧
      (∀ A : Finset (Zd 3 (sz0.L n)), A.Nonempty →
        Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E A (sz0.seqXmat n ω)} ≤
          queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10))

-- statement of `inst_QDiff` (probe `:2154`)
example (h : QDiff_pin) : Prop :=
    ∀ᶠ n in atTop,
      (Sizes.seqP sz0 {ω | qd1Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ))) ∧
       Sizes.seqP sz0 {ω | qd2Bad sz0 (1 / 10) (1 / 20) (1 / 10) n ω} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))) ∧
      ∀ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z → ∀ a b : Zd 3 (sz0.L n),
        ‖(∫ ω, avg2 sz0 n (fun x y => ((‖sz0.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
            profPM sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im ∧
        ‖(∫ ω, avg2 sz0 n (fun x y => sz0.Gn n z ω x y * sz0.Gn n z ω y x) a b ∂(Sizes.seqP sz0)) -
            profPP sz0 n z a b‖ ≤ qdBoundExp sz0 n (1 / 10) z.im

-- statement of `inst_BUniv` (probe `:2167`)
example (h : BUniv_pin) : Prop :=
    Tendsto (fun n =>
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Sizes.seqXmat_isHermitian sz0 n ω).eigenvalues ∂(Sizes.seqP sz0)) -
      (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 0 (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues
        ∂(gueP 3 (sz0.L n) (sz0.W n)))) atTop (𝓝 0)

-- statement of `inst_bridge_loc` (probe `:2175`)
example (h : locSC_pin) : Prop :=
    ∀ᶠ n in atTop, Sizes.seqP sz0 {ω | ∃ z : ℂ, sz0.locDomain (1 / 10) (1 / 20) n z ∧ ∃ a : Zd 3 (sz0.L n),
          ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * sz0.Bctl n (1 - z.im) <
            ‖(((sz0.W n : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (sz0.L n) (sz0.W n) a,
                Gres (Sizes.seqXmat sz0 n ω) z true x x - msc z‖} ≤
        ENNReal.ofReal (Nsz sz0 n ^ (-(2 : ℝ)))

-- statement of `inst_bridge_que` (probe `:2185`)
example (h : QUE_pin) : Prop :=
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 → ∀ a : Zd 3 (sz0.L n),
      Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
        queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)

-- statement of `domain_extreme` (probe `:2367`)
example : Prop :=
  sz0.locDomain 2 1 0 Complex.I ∧ ¬ sz0.locDomain 3 (1 / 20) 0 zI ∧
    ¬ sz0.locDomain (1 / 10) 2 0 zI

-- statement of `locBad1_empty_kappa` (probe `:2378`)
example (n : ℕ) (ω : sz0.SeqΩ) : Prop :=
  ¬ locBad1 sz0 3 (1 / 20) (1 / 10) n ω

-- statement of `im_mE_edge` (probe `:2382`)
example {κ : ℝ} : Prop :=
  (mE (2 - κ)).im = Real.sqrt (κ * (4 - κ)) / 2 ∧
    (mE (-(2 - κ))).im = Real.sqrt (κ * (4 - κ)) / 2

-- statement of `que2BadMat_univ` (probe `:2397`)
example {d L W : ℕ} [NeZero L] [NeZero W] (lam ε₀ c E : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ¬ que2BadMat d L W lam ε₀ c E Finset.univ M

-- statement of `que2BadMat_empty_zero` (probe `:2427`)
example {d L W : ℕ} [NeZero L] [NeZero W] (lam ε₀ c : ℝ) (hW : (1 : ℝ) ≤ W) (hlam : 0 ≤ lam) : Prop :=
    que2BadMat d L W lam ε₀ c 0 ∅ (0 : Matrix (Idx d L W) (Idx d L W) ℂ)

-- statement of `inst_calB` (probe `:2461`)
example : Prop :=
    calB sz0 0 (1 / 2) 0 = sz0.Bctl 0 (1 - 1 / 2) ∧
      (((sz0.size 0 : ℕ) : ℝ) * (1 / 2))⁻¹ ≤ calB sz0 0 (1 / 2) 0

-- statement of `inst_distB_compare` (probe `:2469`)
example (a b : Zd 3 (sz0.L 0)) : Prop :=
    (((3 : ℕ) : ℝ) ^ (3 - 2))⁻¹ * calB sz0 0 (1 / 2) (distB sz0 0 a b) ≤
        calB sz0 0 (1 / 2) (((sz0.W 0 : ℕ) : ℝ) * ((zdistD 3 (sz0.L 0) (a - b) : ℕ) : ℝ)) ∧
      calB sz0 0 (1 / 2) (((sz0.W 0 : ℕ) : ℝ) * ((zdistD 3 (sz0.L 0) (a - b) : ℕ) : ℝ)) ≤
        calB sz0 0 (1 / 2) (distB sz0 0 a b)

end Inst

end RBM.Endpoints.T2210Check
