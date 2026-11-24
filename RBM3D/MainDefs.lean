module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Order.Fin.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
# The definitions used by the main statements

Every definition that the statements of `Challenge.lean` use, moved unchanged from the files
named in the section headings. This file depends on Mathlib only; the definition part of
`Challenge.lean` is a copy of it.
-/

/-! ### From `RBM3D/Defs/Lattice.lean` -/

section

namespace RBM

/-- Graph distance from `u` to `0` on the cycle `ZMod L`. -/
def zdist (L : ℕ) (u : ZMod L) : ℕ := min u.val (L - u.val)

/-- The lattice `Z_L^d` of the paper.  `abbrev` so that the `Pi` instances --
`AddCommGroup`, `Fintype`, `DecidableEq` -- are found by instance search. -/
abbrev Zd (d L : ℕ) : Type := Fin d → ZMod L

/-- The periodic `ℓ¹` distance to the origin on `Z_L^d`; it dominates the paper's `L^∞` distance
`zdistInf` of `Defs/Sizes.lean`. -/
def zdistD (d L : ℕ) (x : Zd d L) : ℕ := ∑ i, zdist L (x i)

end RBM

end

/-! ### From `RBM3D/Defs/Block.lean` -/

section

namespace RBM

open Matrix

variable (d L : ℕ) (g : ℝ)

/-- The generating kernel of `S^(B)(g)`. -/
noncomputable def sbKernel : Zd d L → ℂ := fun x =>
  if x = 0 then ((1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ)
  else if zdistD d L x = 1 then ((g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ : ℝ) : ℂ)
  else 0

/-- The block variance matrix `S^(B)(g)` of `(eq:variancematrix)`. -/
noncomputable def SB : Matrix (Zd d L) (Zd d L) ℂ := circulant (sbKernel d L g)

variable [NeZero L]

section Stochastic

/-- The kernel of `S^(B)(g)` as a real function, split into its two pieces. -/
noncomputable def sbKernelR (x : Zd d L) : ℝ :=
  (if x = 0 then (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ else 0) +
    (if zdistD d L x = 1 then g ^ 2 * (1 + 2 * (d : ℝ) * g ^ 2)⁻¹ else 0)

omit [NeZero L] in
theorem sbKernelR_nonneg (x : Zd d L) : 0 ≤ sbKernelR d L g x := by
  unfold sbKernelR
  have : 0 < 1 + 2 * (d : ℝ) * g ^ 2 := by positivity
  split_ifs <;> positivity

end Stochastic

end RBM

end

/-! ### From `RBM3D/Defs/Semicircle.lean` -/

section

namespace RBM

open Complex

section msc

/-- A square root of `z² - 4`. -/
noncomputable def mscDisc (z : ℂ) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (k := ℂ) (z ^ 2 - 4) (n := 2) (by norm_num))

/-- The two roots of `m² + z m + 1 = 0`. -/
noncomputable def mscRoot₁ (z : ℂ) : ℂ := (-z + mscDisc z) / 2

noncomputable def mscRoot₂ (z : ℂ) : ℂ := (-z - mscDisc z) / 2

/-- The Stieltjes transform of the semicircle law: the root of `m² + z m + 1 = 0` with
positive imaginary part (for `Im z > 0`). -/
noncomputable def msc (z : ℂ) : ℂ := if 0 < (mscRoot₁ z).im then mscRoot₁ z else mscRoot₂ z

end msc

end RBM

end

/-! ### From `RBM3D/Propagator/Basic.lean` -/

section

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (g : ℝ)

section Defs

/-- (2.60) `def_Thxi` for the random band matrix model, with spectral parameter
`ξ = t · m(σ₁)m(σ₂)`: the propagator `Θ_ξ = (1 - ξ S^(B))⁻¹`. -/
noncomputable def Theta (ξ : ℂ) : Matrix (Zd d L) (Zd d L) ℂ :=
  Ring.inverse (1 - ξ • SB d L g)

end Defs

end RBM

end

/-! ### From `RBM3D/Propagator/Props4.lean` -/

section

namespace RBM

open Matrix
open scoped NNReal Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L] (g : ℝ)

section Real

/-- `S^(B)(g)` as a real matrix. -/
noncomputable def SBR : Matrix (Zd d L) (Zd d L) ℝ :=
  Matrix.of fun a b => sbKernelR d L g (a - b)

end Real

end RBM

end

/-! ### From `RBM3D/Gauss/Model.lean` -/

section

namespace RBM.Gauss

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable (d L W : ℕ) (g : ℝ)

/-- A vertex of the fine lattice: the block it lies in, and its position inside that block.
The paper writes `x ∈ [a]`; here `x.1 = a`. -/
abbrev Vtx : Type := Zd d L × Fin (W ^ d)

end RBM.Gauss

end

/-! ### From `RBM3D/Defs/Sizes.lean` -/

section

noncomputable section

open Filter

namespace RBM.Gauss

section Lattice

variable (d L W : ℕ)

/-- The fine lattice `Z_{WL}^d` of Section 2. -/
abbrev Idx : Type := Zd d (W * L)

/-- The block (coordinate in `Z_L`) of a one-dimensional coordinate of `Z_{WL}`
((2.2) `eq:blockIa`; blocks are numbered from zero). -/
def blk (i : ZMod (W * L)) : ZMod L := ((i.val / W : ℕ) : ZMod L)

variable [NeZero L] [NeZero W]

/-- The offset inside a one-dimensional block ((2.2) `eq:blockIa`). -/
def ofs (i : ZMod (W * L)) : Fin W := ⟨i.val % W, Nat.mod_lt _ (NeZero.pos W)⟩

/-- Block label and offset of a lattice point, coordinatewise ((2.2) `eq:blockIa`);
the offset is stored in `Fin (W^d)` so that the target is the block-product index `Vtx d L W`. -/
def split (i : Idx d L W) : Vtx d L W :=
  (fun k => blk L W (i k), finFunctionFinEquiv (fun k => ofs L W (i k)))

/-- The block `[a] = {x : x ∈ block a}` of (2.2) `eq:blockIa`; it has `W^d` points. -/
def Iblk (a : Zd d L) : Finset (Idx d L W) :=
  Finset.univ.filter fun x => (split d L W x).1 = a

end Lattice

/-- The paper's `|x|` is the periodic `L^∞` norm (Section 2 after (2.3) `representativeL`,
`|x-y| ≡ ‖[x-y]_{WL}‖_∞`); `zdistD` (`Defs/Lattice.lean`) is the `ℓ¹` norm.  This one is used for
the stochastic and endpoint statements, `zdistD` for the propagator side. -/
def zdistInf (d L : ℕ) (x : Zd d L) : ℕ := Finset.univ.sup fun i => zdist L (x i)

/-- **The size data of an admissible sequence** (Section 2, (2.10) `eq:WO`).
`L n`, `W n`: the number and the side of the blocks at size index `n`; `lam n`: the coupling
`g = λ^{-1}` of (2.1) `def:ilambda`, passed as the `g` argument of `SB`, `ellT`, `Bparam`.
**`lam` is a sequence**; nothing here fixes it (it may tend to `0`); (2.10) `eq:WO` is the
separate predicate `Sizes.WO`.  The dimension `d` is the parameter of the structure. -/
structure Sizes (d : ℕ) where
  /-- number of blocks per side, `L ≥ 3` -/
  L : ℕ → ℕ
  /-- block side, `W ≥ 1` -/
  W : ℕ → ℕ
  /-- the coupling `g = λ^{-1}` of (2.1) `def:ilambda` -/
  lam : ℕ → ℝ
  three_le_L : ∀ n, 3 ≤ L n
  W_pos : ∀ n, 0 < W n

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

instance neZeroL (n : ℕ) : NeZero (sz.L n) :=
  ⟨(Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) (sz.three_le_L n)).ne'⟩
instance neZeroW (n : ℕ) : NeZero (sz.W n) := ⟨(sz.W_pos n).ne'⟩

/-- **The scale `N = (W L)^d`** (Section 2): the matrix dimension, and the one scale parameter of
every `≺` in `Defs/StochDomAt`. -/
def size (n : ℕ) : ℕ := (sz.W n * sz.L n) ^ d

/-- (2.10) `eq:WO`: `W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1}`, eventually along the sequence. -/
def WO (𝔡 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹

/-- (2.9) `Main_DEL_COND`: `W ≥ N^𝔠`, eventually. -/
def Bandwidth (𝔠 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)

/-- `N → ∞`: the paper's "provided `N` is sufficiently large" (Theorem 2.1, `MR:decol`), made
explicit. -/
def SizeTendsto : Prop := Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop

/-- The standing hypotheses of `MR:decol`, `MR:locSC`, ... (Theorem 2.1): constants `𝔠, 𝔡 > 0`
with `W ≥ N^𝔠` and (2.10) `eq:WO`. -/
def Admissible (𝔠 𝔡 : ℝ) : Prop :=
  0 < 𝔠 ∧ 0 < 𝔡 ∧ sz.SizeTendsto ∧ sz.Bandwidth 𝔠 ∧ sz.WO 𝔡

/-- `𝐃_{κ,ε}` of (2.12) `eq:spectral_domain` at size index `n`; the scale of the lower
bound on `η` is `N = sz.size n`. -/
def locDomain (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  |z.re| ≤ 2 - κ ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1

end Sizes

end RBM.Gauss

end

end

/-! ### From `RBM3D/Gauss/FineModel.lean` -/

section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

section Model

variable (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W]

/-- **`(eq:variancematrix)`** on the fine lattice: `S_xy = W^{-d} S^(B)_{ab}(g)` for `x ∈ [a]`,
`y ∈ [b]`.  The function `svar` of `RBM3D/Gauss/Model.lean` is the same function on `Vtx`; this
one is on `Z_{WL}^d`. -/
def svarF (i j : Idx d L W) : ℝ :=
  ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1

omit [NeZero L] in
theorem svarF_nonneg (i j : Idx d L W) : 0 ≤ svarF d L W g i j :=
  mul_nonneg (by positivity) (sbKernelR_nonneg d L g _)

/-- A finite injective key, used only to orient independent off-diagonal entries (independence up to
`H_xy = conj H_yx`, `(bandcw0)`). -/
def idxKey (i : Idx d L W) : ℕ := (Fintype.equivFin (Idx d L W) i).val

/-- Two real coordinates per oriented pair of lattice points (`(bandcw0)`). -/
abbrev CoordF : Type := Idx d L W × Idx d L W × Bool

/-- The finite product sample space of one size (`(bandcw0)`). -/
abbrev Ω : Type := CoordF d L W → ℝ

/-- Variance of one real coordinate: `S_ii` on the diagonal (one real Gaussian), `S_ij/2` off it
(two real Gaussians), so that `E|X_ij|² = S_ij` (`(bandcw0)`). -/
def gvarF (c : CoordF d L W) : ℝ≥0 :=
  ⟨if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2, by
    split_ifs
    · exact svarF_nonneg d L W g _ _
    · exact div_nonneg (svarF_nonneg d L W g _ _) (by norm_num)⟩

/-- The entry `X_ij` of the Hermitian matrix, oriented by `idxKey`; real on the diagonal
(`(bandcw0)`: `N_ℝ` on the diagonal, `N_ℂ` off it). -/
def Xentry (ω : Ω d L W) (i j : Idx d L W) : ℂ :=
  if idxKey d L W i < idxKey d L W j then
    (ω (i, j, true) : ℂ) + Complex.I * (ω (i, j, false) : ℂ)
  else if idxKey d L W j < idxKey d L W i then
    (ω (j, i, true) : ℂ) - Complex.I * (ω (j, i, false) : ℂ)
  else (ω (i, j, true) : ℂ)

/-- **`H` of `(bandcw0)`** at one size. -/
def Xmat (ω : Ω d L W) : Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.of fun i j => Xentry d L W ω i j

end Model

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- A coordinate records its size index as well as the entry and the real/imaginary tag
(`(bandcw0)`). -/
abbrev SeqCoord : Type := Σ n : ℕ, CoordF d (sz.L n) (sz.W n)

/-- One common sample space for all sizes (`(bandcw0)`; the `≺` of `(stoch_domination)` along
the sequence is one statement on one space). -/
abbrev SeqΩ : Type := SeqCoord sz → ℝ

/-- Coordinate variance at size `n`, with the coupling `sz.lam n` (`(eq:variancematrix)`). -/
def seqGvar (c : SeqCoord sz) : ℝ≥0 := gvarF d (sz.L c.1) (sz.W c.1) (sz.lam c.1) c.2

/-- **The model measure** (`(bandcw0)`, `(eq:variancematrix)`): independent
Gaussian coordinates for every size in one countable product.
Every size projection has the one-size law `PF` (`seqP_map_slice`). -/
def seqP : Measure (SeqΩ sz) := Measure.infinitePi fun c => gaussianReal 0 (seqGvar sz c)

/-- The coordinate vector at size `n`, extracted from the common product (`(bandcw0)`). -/
def slice (n : ℕ) (ω : SeqΩ sz) : Ω d (sz.L n) (sz.W n) := fun c => ω ⟨n, c⟩

/-- **`H` of `(bandcw0)` on the common probability space** at size index `n`. -/
def seqXmat (n : ℕ) (ω : SeqΩ sz) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Xmat d (sz.L n) (sz.W n) (slice sz n ω)

end Sizes

end RBM.Gauss

end

end

/-! ### From `RBM3D/Loop/GLoopFlow.lean` -/

section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

section FlowData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`G_t(σ)`** of `Def:G_loop` for a flow matrix `H` and a flow value `z = z_t`:
`G(+) = (H - z)⁻¹`, `G(-) = (H - z̄)⁻¹ = G(+)^*`.  It is generic in the index type, so it serves
the fine lattice (entries, `(G_bound)`) and the block-product index (loops). -/
def Gres (H : Matrix ι ι ℂ) (z : ℂ) (σ : Bool) : Matrix ι ι ℂ :=
  Ring.inverse (H - (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix ι ι ℂ))

variable (d L W : ℕ) [NeZero L]

variable [NeZero W]

end FlowData

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **`G(z) = (H - z)⁻¹`** of `(def_Green)` for the size-`n` matrix `H` of the model
measure `seqP sz` (the Green function of the endpoints `MR:locSC`, `MR:QuDiff`). -/
def Gn (n : ℕ) (z : ℂ) (ω : SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (seqXmat sz n ω) z true

end Sizes

end RBM.Gauss

end

end

/-! ### From `RBM3D/Induction/Defs.lean` -/

section

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The block label `[x]` of a lattice point `x ∈ Z_{WL}^d` ((2.2) `eq:blockIa`). -/
def STblk (n : ℕ) (x : Idx d (sz.L n) (sz.W n)) : Zd d (sz.L n) :=
  (split d (sz.L n) (sz.W n) x).1

end RBM.Gauss.Sizes

end

end

/-! ### From `RBM3D/Universality/Pins.lean` -/

section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

namespace RBM.Univ

section Vocab

/-- `(μ, ψ)` is an orthonormal eigenbasis of `H`: the vectors `ψ k` are orthonormal and `H ψ k = μ k ψ k`. -/
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop :=
  (∀ k k', star (ψ k) ⬝ᵥ ψ k' = if k = k' then 1 else 0) ∧
    ∀ k, H *ᵥ ψ k = (μ k : ℂ) • ψ k

end Vocab

section Pins

variable {d : ℕ}

/-- The one scale `N = (W L)^d = sz.size n` as a real number. -/
abbrev Nsz (sz : Sizes d) (n : ℕ) : ℝ := ((sz.size n : ℕ) : ℝ)

/-- `𝓘_E(ε₀) = {x : |x - E| ≤ W^{-ε₀} (ilambda W^{d/2} / N)}` of (2.17) `eq:defIE`.  The footnote after
Theorem 2.1 (`MR:decol`) replaces `ilambda` by `ilambda ∧ 1`; only the lower bound
`W^{-ε₀}(lam ∧ 1) W^{d/2} ≥ W^{2𝔡/3}` is used here (`un_window_sub`), which holds for both readings. -/
def queWindow (d L W : ℕ) (lam ε₀ E x : ℝ) : Prop :=
  |x - E| ≤ (W : ℝ) ^ (-ε₀) * (lam * (W : ℝ) ^ ((d : ℝ) / 2) / (((W * L) ^ d : ℕ) : ℝ))

/-- The probability bound `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}` of (2.18) `Meq:QUE`. -/
def queBound (W : ℕ) (𝔡 ε₀ c τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((W : ℝ) ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ))

/-- The failure event of (2.18) `Meq:QUE` at the block `a` for an arbitrary Hermitian
matrix `M` on the fine lattice: some orthonormal eigenbasis has `i, j` in the window `𝓘_E(ε₀)` with
`|∑_{x∈[a]} conj ψ_i(x) ψ_j(x) - (W^d/N) δ_ij| ≥ W^{d-c}/N`. -/
def queBadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (a : Zd d L)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ i j, queWindow d L W lam ε₀ E (μ i) ∧ queWindow d L W lam ε₀ E (μ j) ∧
      (W : ℝ) ^ ((d : ℝ) - c) / (((W * L) ^ d : ℕ) : ℝ) ≤
        ‖(∑ x ∈ Iblk d L W a, star (ψ i x) * ψ j x) -
            ((W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ)) * (if i = j then 1 else 0)‖

end Pins

end RBM.Univ

end

end

/-! ### From `RBM3D/Endpoints.lean` -/

section

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints

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

end Endpoints

end RBM.Endpoints

end

end
