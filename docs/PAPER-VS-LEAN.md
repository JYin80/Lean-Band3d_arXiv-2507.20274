# The paper and the Lean proof: detailed differences

**Paper.** S. Dubova, F. Yang, H.-T. Yau and J. Yin, *Delocalization of non-mean-field random matrices in
dimensions d ≥ 3*, arXiv:2507.20274, in the version `paper/DubovaYangYauYin_RBM3D_Lean_version.pdf` of this
repository (TeX source in `paper/tex/`). Page, equation and theorem numbers below refer to this PDF.

**Cited works.** [LANDON20191137] = B. Landon, P. Sosoe, H.-T. Yau, *Fixed energy universality of Dyson Brownian
motion*, Adv. Math. 346 (2019), in the form of arXiv:1609.09011v4; it is the one external input (§4). The PDF does
not cite it directly: it cites it through [28]. [28] = S. Dubova, K. Yang, H.-T. Yau, J. Yin, *Delocalization of
two-dimensional random band matrices*, arXiv:2503.07606. [59] = S. K. Truong, F. Yang, J. Yin, *On the localization length of finite-volume random block Schrödinger operators*,
arXiv:2503.11382. [64] = C. Xu, F. Yang, H.-T. Yau, J. Yin, *Bulk universality and quantum unique ergodicity for random band
matrices in high dimensions*, Ann. Probab. 52 (2024). [69] = H.-T. Yau, J. Yin, *Delocalization of one-dimensional random band
matrices*, arXiv:2501.01718. (Numbers in brackets are those of the bibliography of the PDF, pp. 104-106.)

**Lean.** The library is `RBM3D` (Lean 4.34.0, Mathlib v4.34.0); its declarations are in the namespace `RBM`. Every
name below that starts with `RBM.` is a declaration of this library. Other names (such as `Matrix.trace`,
`ProbabilityTheory.gaussianReal`) are from Mathlib. Lean text quoted below is copied from the source files by a
script, without docstrings.

---

## 1. What is proved

**The band model.** A *size sequence* is a term `sz : RBM.Gauss.Sizes d` for a dimension `d`: block numbers `L n ≥ 3`, block sides `W n ≥ 1` and
couplings `lam n`, the paper's `g` of (2.1) (`g = λ^{-1}`). The matrix dimension is `sz.size n = (W n · L n)^d`, the paper's `N = (WL)^d` (p. 7). The torus
`Z_{WL}^d` is `RBM.Gauss.Idx d L W = RBM.Zd d (W * L)`, with `RBM.Zd d m = Fin d → ZMod m`; the block lattice `Z_L^d` is `RBM.Zd d L`, and the block `[a]` of (2.2) is
`RBM.Gauss.Iblk d L W a`, a set of `W^d` points (`RBM.Gauss.card_Iblk`). The matrix `S^{(B)}(g)` of (2.5) is `RBM.SB d L g`, the circulant matrix of the kernel
`RBM.sbKernel`: `(1 + 2dg²)^{-1}` at `a = b` and `g²(1 + 2dg²)^{-1}` at the nearest neighbours `a ∼ b` (`zdistD d L (a - b) = 1`); for `L ≥ 3` there are `2d` of
them (`RBM.card_nbhd`) and the kernel has total mass `1` (`RBM.sum_sbKernelR`, `RBM.norm_SB`). The variance of (2.4) is `S_xy = W^{-d} S^{(B)}_{ab}` for `x ∈ [a]`, `y ∈ [b]`: `RBM.Gauss.svarF d L W g x y`
(through the real form `RBM.SBR` of `S^{(B)}`). The matrix `RBM.Gauss.Xmat d L W ω` is Hermitian (`RBM.Gauss.Xmat_isHermitian`); its real coordinates are independent centred
Gaussians with the law `RBM.Gauss.PF d L W g`, of variance `S_xx` for the diagonal entry and `S_xy/2` for the real and the imaginary part of an off-diagonal entry. For a size
sequence, `RBM.Gauss.Sizes.seqP sz` is the product of these laws over all `n`, and the law of the matrix `sz.seqXmat n` is `PF d (L n) (W n) (lam n)`
(`RBM.Gauss.Sizes.seqP_map_slice`). All probabilities are `Sizes.seqP sz` of sets. The standing assumptions (2.9), (2.10) together with `N → ∞` are `Admissible`; `locDomain` is
`𝐃_{κ,ε}` of (2.12).

```lean
-- namespace RBM.Gauss; the definitions after `Sizes` are in `namespace Sizes`, with `sz : Sizes d`
structure Sizes (d : ℕ) where
  L : ℕ → ℕ
  W : ℕ → ℕ
  lam : ℕ → ℝ
  three_le_L : ∀ n, 3 ≤ L n
  W_pos : ∀ n, 0 < W n
def size (n : ℕ) : ℕ := (sz.W n * sz.L n) ^ d
def WO (𝔡 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹
def Bandwidth (𝔠 : ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)
def SizeTendsto : Prop := Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop
def Admissible (𝔠 𝔡 : ℝ) : Prop :=
  0 < 𝔠 ∧ 0 < 𝔡 ∧ sz.SizeTendsto ∧ sz.Bandwidth 𝔠 ∧ sz.WO 𝔡
def locDomain (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  |z.re| ≤ 2 - κ ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
-- namespace RBM.Gauss, with `(d L W : ℕ) (g : ℝ)`
def svarF (i j : Idx d L W) : ℝ :=
  ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 (split d L W j).1
```

**The block Anderson model** (Section 2.2, p. 11). It uses the same size sequence `sz`. The potential `V` is the band
matrix of the size sequence `sz.withLam 0` (coupling `0`, so `S^{(B)}(0) = I`, (2.29)); `Ψ = Ψ^{(B)} ⊗ I_{W^d}` of (2.31) is
`RBM.Gauss.PsiI d L W` (`RBM.Gauss.PsiB` is `Ψ^{(B)}`, the adjacency matrix of the block lattice); and `H = V + gΨ` of (2.30)
is `sz.seqHBA n ω`, on the probability space of the potential, `Sizes.seqP (sz.withLam 0)`. Equation (2.32) is
`RBM.BA.BASelf d L g z m`; its solution for `Im z > 0` is `RBM.BA.BAm d L g z` (it exists and is unique:
`RBM.BA.BASelf_exists`, `RBM.BA.BASelf_unique`). `RBM.BA.BAMz` is `M(z)` of (2.33), `RBM.BA.BArho d L g E` is the density
`ρ_N(E)`, and `RBM.BA.BAbulk d L g κ E` is `E ∈ B_κ` of (2.34) (§2.10).

```lean
-- namespace RBM.BA, with `(d L : ℕ) [NeZero L]`
def BASelf (g : ℝ) (z m : ℂ) : Prop :=
  0 < m.im ∧ m = (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace
def BAm (g : ℝ) (z : ℂ) : ℂ :=
  haveI := Classical.propDecidable (∃ m, BASelf d L g z m)
  if h : ∃ m, BASelf d L g z m then h.choose else 0
def BArho (g E : ℝ) : ℝ := (BAm d L g (E : ℂ)).im / Real.pi
def BAbulk (g κ E : ℝ) : Prop := κ ≤ BArho d L g E
```

**The theorems.** The statements `decol`, `locSC`, `QUE`, `QDiff`, `BUniv` are in `RBM3D/Endpoints.lean` (Appendix A).
The four theorems without hypothesis are proved in `RBM3D/Main/BandTerminal.lean`, and so is Theorem 2.4 from `UNL32`
(`BUniv_of_L32`, which applies the assembly `bUniv_holds` of `RBM3D/Main/BUnivHolds.lean` to the proved leaves). Theorem 2.7 at dimension `d` is `RBM.BA.BAThm27L d` (`RBM3D/BA/MAPins.lean`), proved in
`RBM3D/BA/UNBUniv.lean`; the final theorem is in `RBM3D/Main/FinalShape.lean`.

| Paper | Lean statement | Lean theorem | Hypotheses other than parameters |
|---|---|---|---|
| Theorem 2.1 (delocalization), p. 8 | `RBM.Endpoints.decol` | `RBM.Endpoints.decol_holds` | none |
| Theorem 2.2 (local semicircle law (2.14), (2.15)), p. 8 | `RBM.Endpoints.locSC` | `RBM.Endpoints.locSC_holds` | none |
| Theorem 2.3 (QUE (2.18), (2.19)), p. 9 | `RBM.Endpoints.QUE` | `RBM.Endpoints.QUE_holds` | none |
| Theorem 2.4 (bulk universality (2.20)), p. 9 | `RBM.Endpoints.BUniv` | `RBM.Endpoints.BUniv_of_L32 : RBM.Univ.UNL32 → BUniv` | `RBM.Univ.UNL32` |
| Theorem 2.5 (quantum diffusion (2.22)-(2.25)), pp. 9-10 | `RBM.Endpoints.QDiff` | `RBM.Endpoints.QDiff_holds` | none |
| Theorem 2.7 (block Anderson model), p. 11 | `RBM.Endpoints.Thm27` | `RBM.Endpoints.Thm27_of_L32 : RBM.Univ.UNL32 → Thm27` | `RBM.Univ.UNL32` |

```lean
-- namespace RBM.Endpoints (RBM3D/Main/FinalShape.lean), with `open RBM.Univ`
def Thm27 : Prop := ∀ d : ℕ, 3 ≤ d → RBM.BA.BAThm27L d
theorem Thm27_of_L32 : RBM.Univ.UNL32 → Thm27
theorem final_shape : RBM.Univ.UNL32 →
    (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
-- namespace RBM.BA (RBM3D/BA/UNBUniv.lean), with `open RBM.Univ`
theorem baThm27L_all (h32 : UNL32) : ∀ d : ℕ, 3 ≤ d → BAThm27L d
theorem baThm27L_three : UNL32 → BAThm27L 3
```

The band half of `final_shape` is `RBM.Endpoints.band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff`. "Parameters" are `d ≥ 3`, `𝔠, 𝔡`, a size sequence
`sz : Sizes d` with `sz.Admissible 𝔠 𝔡`, and `κ, τ, D > 0` (`κ, ε, τ, D` in Theorems 2.2 and 2.5; `κ, ε₀, c, τ` in Theorem 2.3, with `0 < ε₀ < 𝔡/2`, `0 < c < ε₀`, `c < 𝔡/5`); in
Theorem 2.4 also `k ≥ 1`, `|E| ≤ 2 − κ` and the test function `O`, and in Theorem 2.7 also `E, E'` as in §2.11. The spectral parameter `z`, the energy `E`, the blocks `a, b` and the block
set `A` are bound inside the statements (§2.5).

**Dimension.** All six results are proved for every `d ≥ 3`, as the paper states ("Fix any dimension `d ≥ 3`", Theorems 2.1 and 2.7, pp. 8 and 11). The band statements begin with
`∀ d : ℕ, 3 ≤ d →`, and Theorem 2.7 is `Thm27 := ∀ d, 3 ≤ d → BAThm27L d`, proved by `RBM.BA.baThm27L_all` from `UNL32` and `RBM.BA.baStep5III_holds_any`, the proved case (iii)
(`1 − s ≥ 1 − t ≥ g²`, p. 45) of Step 5 of the induction for the block Anderson model at each `d`. The case `d = 3` is `RBM.BA.baThm27L_three`.

**The single external input.** Theorems 2.4 and 2.7 are proved from `RBM.Univ.UNL32`, which is [LANDON20191137, Theorem 2.2]
for complex Hermitian matrices, written at unit density (§4). It is a hypothesis of `BUniv_of_L32`, `Thm27_of_L32` and
`final_shape`, not an axiom. Theorems 2.1, 2.2, 2.3 and 2.5 use no external input. The results that the paper quotes from
[28], [64], [69] and the other cited works are not assumed in Lean; the corresponding Lean proofs are listed in §5.

**Axioms.** The command `#assert_rbm_axioms` (file `RBM3D/Test/Axioms.lean`, run as the last command of `RBM3D.lean`) walks
every constant of the environment whose name starts with `RBM`, computes the axioms it depends on (as `#print axioms` does) and
fails the build unless each of them is `propext`, `Classical.choice` or `Quot.sound`. There is no further allowed axiom. The command also fails
if it finds fewer than `100` such constants, so that a mistyped namespace cannot make the audit pass vacuously. In particular no `sorry` and no declared `axiom`
occurs in `RBM`; every statement that is not proved is a hypothesis, a theorem parameter or a structure field. The command `#print axioms` on the theorems of the table, on `band_terminal`, `final_shape`,
`baThm27L_all` and `baThm27L_three` prints

```
'RBM.Endpoints.decol_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.locSC_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QUE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QDiff_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.BUniv_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.band_terminal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Thm27_of_L32' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.final_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThm27L_three' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**The statements are not vacuous.** The theorems of the table are applied at concrete data by compiled `example`s. In `BandTerminal.lean` and `FinalShape.lean`, `UNL32` is the only hypothesis
left, and the four theorems without hypothesis are applied with none; the examples of `BUnivHolds.lean` and `MAPins.lean` apply the intermediate statements `bUniv_holds` and `BAThm27L 3`.
- `RBM3D/Main/BandTerminal.lean`, §Instances. The size sequence `RBM.Gauss.SizesInst.sz0`: `d = 3`, `L n = 4(n+1)`, `W n = (2(n+1))^5`, `lam n = (2(n+1))^{-6}` (`L = 4`, `W = 32`,
  `N = 2097152` at `n = 0`), admissible at `(𝔠, 𝔡) = (1/6, 1/10)` (`sz0_admissible`). With `κ = 1/10`: `decol` at `(τ, D) = (1/10, 1)`; `locSC` and `QDiff` at `(ε, τ, D) = (1/20, 1/10, 2)`;
  `QUE` at `(ε₀, c, τ) = (1/30, 1/60, 1/10)`; `BUniv` at `k = 1`, `E = 0` and the bump function `RBM.Univ.UNInst.bump` (smooth, `1` on `‖x‖ ≤ 1`, supported in `‖x‖ < 2`). One example applies the
  four unconditional theorems at this data with no hypothesis.
- `RBM3D/Main/BUnivHolds.lean`. Two examples apply `bUniv_holds` at `sz0`, `k = 1`, `κ = 1/10` and `bump`, at `E = 0` and at the edge `E = 19/10 = 2 − κ`; the leaves of `bUniv_holds` are
  hypotheses of these examples.
- `RBM3D/BA/MAPins.lean`. The class sequence `RBM.Univ.BAInst.S0`: `d = 3`, `L n = 4`, `W n = (2(n+1))^5`, a constant coupling `g₀ ∈ (0, 3/10]` taken from a real-axis solution of (2.32)
  (`RBM.BA.UNPinsInst.fp`), admissible at `(1/6, 1/10)`, with `κ_* = Im m₀/π > 0` and an energy `E_*` with `κ_* ≤ ρ_N(E_*)` for every `n` (the bulk is nonempty). The five conjuncts of
  `BAThm27L 3` are applied at `S0` at `κ_*`, with `E_*`, `k = 1`, `E' = 0` and `bump` in the universality conjunct; further examples apply the fixed-`z`, step and per-`d` statements of the file at `S0`.
- `RBM3D/Main/FinalShape.lean`. The ten conjuncts of `final_shape` are applied at the data above (five at `sz0`, five at `S0`; the `d = 3` conjuncts of `Thm27` are `.2 3 le_rfl`), all at once,
  with `UNL32` the only hypothesis. A further example applies the `d = 4` part of `Thm27`, that is `(final_shape h32).2 4`, to concrete data over a nonempty bulk. The data are a size sequence in
  `Sizes 4` with `L n = 4`, `W n = (2(n+1))^5` and the constant coupling `lam n = g₀`, admissible at `(𝔠, 𝔡) = (1/8, 1/10)` (the proof of `Admissible (1/8) (1/10)` is in the file, for every
  `g₀ ∈ (0, 10]`), and a triple `(g₀, E, κ)` with `0 < g₀ ≤ 3/10`, `κ > 0` and `BAbulk 4 4 g₀ κ E`, obtained from a real-axis solution of (2.32) at `(d, L) = (4, 4)` (the private lemma
  `FinalShape_bulk4`, using `RBM.BA.BAbulk_iff_exists`). The bulk is nonempty: `κ ≤ ρ_N(E)` holds for every `n`, and the end domain `BAendDom` (§2.12) is nonempty at every `n`. The coupling is the
  constant `g₀` because the witness of the bulk is built at one fixed coupling, so a constant sequence is an eventual witness directly. All five conjuncts of `Thm27 4` (decol, locSC, QUE, BUniv, QDiff) are applied at this
  data, the universality conjunct at `k = 1`, `E' = 0` and `RBM.Univ.UNInst.bump`, with `UNL32` the only hypothesis.

---

## 2. Differences between the statements

Each entry gives the paper's wording, the Lean form and the relation. "Equivalent": each statement implies the other for the
full family of parameters. "Lean stronger": the Lean statement implies the paper's. "Identical": the same statement up to
notation.

### 2.1 Size sequences instead of "`N` sufficiently large" (equivalent, with §3)

- **Paper** (pp. 8-10, (2.9), (2.10)): assume there are constants `𝔠, 𝔡 > 0` with `W ≥ N^𝔠` and `W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1}`; then for any small `κ, τ > 0` and large `D > 0` the estimate
  holds "provided `N` is sufficiently large" (Theorem 2.1) or "for large enough `N`" (Theorems 2.2, 2.5); Theorem 2.4 has `lim_{N→∞}`.
- **Lean.** `∀ d, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ τ D, … → ∀ᶠ n in atTop, …`, with `N = sz.size n`.
  `Admissible` contains `N → ∞` and (2.9), (2.10) for large `n`. The divergence of `N` is explicit because "for large `n`" along a
  bounded sequence of sizes has no content; in the paper it is part of "`N` sufficiently large". The triple `(W, L, g)` of the
  paper is `(W n, L n, lam n)`, so `g` may depend on `n`, as in (2.10). The constants `𝔠, 𝔡, κ, ε, τ, D` (and `ε₀, c` in
  Theorem 2.3) are fixed before `n`.

### 2.2 Blocks, coordinates, variance profile and `L ≥ 3` (identical up to a translation; standing assumption)

- **Paper** (p. 7, (2.2)-(2.5)): `Z_{WL}^d := ⟦−WL/2+1, WL/2⟧^d`, `Z_L^d := ⟦−L/2+1, L/2⟧^d`, `[a] := ∏_i ⟦(a(i)−1)W+1, a(i)W⟧` (a footnote treats odd `L`);
  `H_xy ∼ 𝒩_ℝ(0,S_xy)1_{x=y} + 𝒩_ℂ(0,S_xy)1_{x≠y}`, independent up to `H_xy = conj H_yx`; `S_xy = W^{-d} S^{(B)}_{ab}(g)`. The paper states no lower bound on `L`.
- **Lean.** Coordinates lie in `ZMod (W L)`; the block of a coordinate `i` is `i.val / W` (`RBM.Gauss.blk`) and `[a]` is the set of `x` with block label `a` (`RBM.Gauss.Iblk`;
  `RBM.Gauss.splitEquiv : Idx d L W ≃ Vtx d L W`, `Vtx d L W = Zd d L × Fin (W^d)`): blocks are zero-based. For `idxKey i < idxKey j` the entry `H_ij` is
  `ω(i,j,true) + I·ω(i,j,false)` (`RBM.Gauss.Xentry`), the entry below the diagonal is fixed by `H_ji = conj H_ij`, and a diagonal entry is `ω(i,i,true)`. The field `three_le_L` of `Sizes`
  requires `L n ≥ 3`.
- **Relation.** The blocks agree under `x ↦ x − 1`, `a ↦ a − 1`; the profile depends on `a − b` only, so all statements are invariant, and the parity convention is irrelevant for
  `ZMod L`. A diagonal entry is real (`H_xx = conj H_xx`) and `E|H_xx|² = S_xx` fixes its variance; everywhere `E|H_xy|² = S_xy`; the coordinates that `Xentry` never reads do not change
  the law of `H`. For `L ≤ 2` the printed `S^{(B)}` is not doubly stochastic (for `L = 2` a block has `d` neighbours, not `2d`), against the paper's requirement on `S` (p. 7); the Lean
  statements do not cover `L ≤ 2`.

### 2.3 Eigenvalue and eigenvector labels (Lean stronger)

- **Paper** (p. 7): `λ_1 ≤ … ≤ λ_N` with normalized eigenvectors `ψ_k`; (2.11), (2.18), (2.19) use `λ_k`, `ψ_k`.
- **Lean.** `RBM.Univ.IsOrthoEigenbasis H μ ψ`: the `ψ k` are orthonormal and `H ψ_k = μ_k ψ_k`, with no order on `μ`. The failure
  events `decolBad`, `queBadMat`, `que2BadMat` (Appendix A) quantify over every such pair `(μ, ψ)`; for example `decolBad` is
  "there is an orthonormal eigenbasis and a `k` with `|μ_k| ≤ 2 − κ` and `‖ψ_k‖²_∞ > N^{-1+τ}`".
- **Relation.** The paper's failure event, for any choice of its eigenvectors, is contained in the Lean failure event, so the
  Lean bound implies the paper's. The order is irrelevant, since each statement takes a maximum over all labels.

### 2.4 Failure probability instead of success probability (equivalent)

- **Paper** (Theorems 2.1, 2.2, 2.5): the event holds "with probability `≥ 1 − N^{-D}`"; Theorem 2.3: `P(bad event) ≤ W^{…}`.
- **Lean.** `Sizes.seqP sz {ω | …bad…} ≤ ENNReal.ofReal (N^{-D})`, the set being the exact complement of the paper's event (for
  example `decolBad`); in Theorem 2.3 the bad event itself.
- **Relation.** For a measurable event `B`, `P(B) ≥ 1 − x` if and only if `P(Bᶜ) ≤ x`. Without measurability, `seqP` of a set is its
  outer measure, and `1 ≤ P(B) + P(Bᶜ)` still gives `P(B) ≥ 1 − N^{-D}`.

### 2.5 Uniformity in `z`, `E`, `a`, `A`; unions inside the probability (identical; equivalent, with §3)

- **Paper.** Theorem 2.2 (p. 8): the events (2.14), (2.15) are `⋂_{z ∈ 𝐃_{κ,ε}}` (and `⋂_{x,y}`, resp. `max_a`) and hold "with probability `≥ 1 − N^{-D}` for large enough `N`"; the domain
  `𝐃_{κ,ε}` of (2.12) depends on `N`, so the threshold cannot depend on `z`. Theorem 2.5: (2.22), (2.23) hold "with probability `≥ 1 − N^{-D}` for all `a, b ∈ Z_L^d`"; (2.24), (2.25) hold
  "for each `z ∈ 𝐃_{κ,ε}`", with `max_{a,b}`. Theorem 2.3: `sup_{E:|E|≤2−κ}` and `max_a`, "provided `N` is large enough".
- **Lean.** `locBad1`, `locBad2`, `qd1Bad`, `qd2Bad` are `∃ z, locDomain … ∧ …`, with the quantifiers over `x, y` (resp. `a`, resp.
  `a, b`) inside the event: the unions over `z`, `x, y`, `a`, `b` are inside the probability. `QUE` is `∀ᶠ n, ∀ E, |E| ≤ 2 − κ → (∀ a, …) ∧
  (∀ A, A.Nonempty → …)`, and the expectation half of `QDiff` is `∀ᶠ n, ∀ z, locDomain … → ∀ a b, …`.
- **Relation.** The `⋂_z` inside the probability is the text of (2.14), (2.15), (2.22), (2.23): identical. The threshold uniform in
  `z, E, a, A` is the reading in which thresholds depend on the constants only (§3), equivalent to "for every sequence `z_n ∈ 𝐃_{κ,ε}`
  of the size `N_n`" (and likewise for `E_n, a_n, A_n`). The step from sequences to a uniform threshold is the compiled diagonal
  argument `RBM.Endpoints.eventually_forall_of_sections` (a property that holds for large `n` along every section `s n ∈ Z n`
  holds eventually for all points of `Z n`), used for Theorems 2.2 and 2.5. For (2.22), (2.23), the reading with `a, b` outside the
  probability follows from the Lean reading, and conversely by a union bound over `L^{2d} ≤ N²` pairs with `D` replaced by `D + 2`.

### 2.6 Theorem 2.3: the window, the bound, and (2.19) for nonempty `A` (identical, except `A ≠ ∅`)

- **Paper** (p. 9, (2.17)-(2.19)): `𝓘_E(ε₀) = {x : |x−E| ≤ W^{-ε₀}(g W^{d/2}/N)}`, `ε₀ ∈ (0, 𝔡/2)`, `0 < c < ε₀ ∧ (𝔡/5)`;
  (2.18): the event `max_{i,j: λ_i,λ_j ∈ 𝓘_E} |∑_{x∈[a]} ψ̄_i(x)ψ_j(x) − (W^d/N)δ_ij| ≥ W^{d−c}/N` has probability `≤ W^{−(2ε₀)∧(2𝔡/5)+2c+τ}`;
  (2.19): "for any subset `A ⊂ Z_L^d`", the event `max_{k:λ_k∈𝓘_E} |∑_{a∈A}∑_{x∈[a]}|ψ_k(x)|² − (W^d/N)|A|| ≥ (W^{d−c}/N)|A|`.
- **Lean.** `queWindow`, `queBadMat`, `que2BadMat` (Appendix A) and `queBound W 𝔡 ε₀ c τ = ENNReal.ofReal (W^{−(2ε₀)∧(2𝔡/5)+2c+τ})`, with
  `0 < ε₀ < 𝔡/2`, `0 < c < ε₀`, `c < 𝔡/5`, `τ > 0`. `QUE` states (2.19) for every `A` with `A.Nonempty`.
- **Relation.** (2.18) is identical, and so is (2.19) for `A ≠ ∅` (the paper's `≥ W^{d−c}…` is Lean's `W^{d−c}… ≤ …`). For `A = ∅` the
  event of (2.19) reads `0 ≥ 0` and holds as soon as `𝓘_E` contains an eigenvalue, so (2.19) is meant for nonempty `A`; its proof
  (p. 10) replaces `E_a` by `|A|^{-1}∑_{a∈A}E_a`. The Lean statement omits `A = ∅`.

### 2.7 The distance in `𝓑_{η,|x−y|}` (equivalent)

- **Paper** (pp. 7-8, (2.13), (2.14)): `|x − y| = ‖[x−y]_{WL}‖_∞` for `x, y ∈ Z_{WL}^d` (the periodic `L^∞` distance), and (2.14) is
  `|G_xy(z) − M_xy(z)|² ≤ W^τ 𝓑_{η,|x−y|}`; in (2.22), (2.23) the distance of blocks is `|a−b| = ‖[a−b]_L‖_∞` and `𝓑_{η,W|a−b|}` appears.
- **Lean.** `RBM.Endpoints.distB sz n a b = W · zdistInf d (L n) (a − b)` (`RBM.Gauss.zdistInf` is the periodic `L^∞` norm of `Zd d L`),
  and `locBad1z` uses `calB … (distB sz n (STblk sz n x) (STblk sz n y))`, the block labels of `x` and `y` in place of `x` and `y`. In
  (2.22), (2.23) `qdBound` uses `distB sz n a b`: identical.
- **Relation.** If `k = |[x] − [y]|_∞` and `K = |x − y|`, then `W(k−1) < K < W(k+1)` (coordinatewise, the offsets inside the blocks
  differ by less than `W`). Hence `(K+W)/(Wk+W) ∈ [1/2, 2]`, and `𝓑_{η,K}` and `𝓑_{η,Wk}` differ by a factor at most `2^{d−2}` (the
  second term of `𝓑` does not depend on `K`). Since `W → ∞`, the factor is absorbed by replacing `τ` by `τ/2` for large `n`.

### 2.8 `m(z)`, `M(z)`, `G(z)`, `Θ` and the profiles (identical)

- **Paper** (pp. 7-9): `G(z) = (H − z)^{-1}` (2.6); `m(z) = (−z + √(z²−4))/2 = ∫_ℝ ρ_sc(x)/(x−z) dx` with `ρ_sc(x) = √((4−x²)_+)/(2π)`
  (2.7); `M(z) = m(z) I_N` (2.8); `Θ^{(+,−)} = (1 − |m|²S^{(B)})^{-1}`, `Θ^{(+,+)} = (1 − m²S^{(B)})^{-1}` (2.21).
- **Lean.** `RBM.msc z` is the root of `m² + zm + 1 = 0` with `Im m > 0` for `Im z > 0`, the closed form of (2.7) with the branch of the square root fixed by `Im m > 0`. `Mband sz n z x y = if x = y then msc z else 0`.
  `Gn n z ω = Gres (seqXmat n ω) z true`, with `Gres H z true = Ring.inverse (H − z)`. `RBM.Theta d L g ξ = Ring.inverse (1 − ξ • SB d L g)`,
  and `ThetaPM`, `ThetaPP` are its values at `ξ = ‖msc z‖²` and `ξ = msc z ^ 2`. Since `‖msc z‖ < 1` for `Im z > 0`
  (`RBM.norm_msc_lt_one`) and `‖SB d L g‖ = 1` (`RBM.norm_SB`), the matrix `1 − ξ S^{(B)}` is invertible and `Ring.inverse` is the
  inverse (`RBM.Theta_mul_of_three_le`). `profPM = ‖msc z‖² Θ^{(+,−)}_{ab}/W^d` and `profPP = msc z² Θ^{(+,+)}_{ab}/W^d`; `calB` is (2.13) (the
  subtraction `d − 2` is in `ℕ`, harmless for `d ≥ 3`); `qdBound` and `qdBoundExp` are the right-hand sides of (2.22), (2.23) and of
  (2.24), (2.25). The integral form of (2.7) is not used in the Lean statements.

### 2.9 Correlation functions, the GUE side of (2.20), test functions, one probability space (equivalent; identical)

- **Paper** (p. 9): `p_H` is the joint symmetrized probability density of the unordered eigenvalues, `p_H^{(n)} = ∫ p_H dλ_{n+1}⋯dλ_N`; `p_GUE^{(n)}` is that of
  an `N × N` GUE matrix; for `O ∈ C_c^∞(ℝ^n)`, `|E| ≤ 2 − κ` and fixed `n`, (2.20) is `lim_{N→∞} ∫ dα O(α)[p_H^{(n)} − p_GUE^{(n)}](E + α_1/N, …, E + α_n/N) = 0`.
- **Lean.** `RBM.Univ.kPoint k O E λ = N^k (N−k)!/N! · ∑_{f : Fin k ↪ ι} O(N(λ_{f(1)} − E), …)` with `N = Fintype.card ι`; `BUniv` says that the difference of the expectations of `kPoint` for
  `sz.seqXmat n` under `Sizes.seqP sz` and for the GUE matrix tends to `0` (Appendix A). `RBM.Univ.gueP d L W` is the law of independent Gaussian coordinates with variance `1/N` on the diagonal and
  `1/(2N)` for each real and imaginary part off the diagonal (`gueVar`), so `Xmat d L W` under it is a GUE matrix with `E|h_ij|² = 1/N`, `N = (WL)^d`, the normalization with the semicircle law on
  `[−2, 2]`. `O` is `IsTestFun`: `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) O` (smooth, not analytic) and `HasCompactSupport O`. The constant `κ` of the setting becomes `∀ κ > 0, ∀ E, |E| ≤ 2 − κ`. One
  product measure `seqP sz` carries the coordinates of all indices `n`; the matrix at index `n` reads only level `n`, and every statement concerns one index at a time.
- **Relation.** If the joint density of the symmetrized eigenvalues exists, then `∫ O(α) p^{(k)}(E + α/N) dα = 𝔼[N^k(N−k)!/N! ∑_{distinct i} O(N(λ_{i_1} − E), …)]`
  (standard; not compiled); the Lean definition does not presuppose a density, and the comparison is with the GUE matrix, not with an
  explicit density. Real-valued `O` is identical to the paper's; complex-valued `O` follow by linearity. One probability space is
  equivalent to a matrix for each `N` (§3).

### 2.10 The bulk of the block Anderson model (identical)

- **Paper** (p. 12, (2.34)): the condition `|E| ≤ 2 − κ` is replaced, for `E = λ_k` in (2.11), `E = Ê` in (2.12) and the energies of Theorems 2.3 and 2.4,
  by `E ∈ B_κ := {E ∈ ℝ : ρ_N(E) ≥ κ}`, `ρ_N(E) = π^{-1} Im m(E + i0_+, g)`; `m` solves (2.32), `N^{-1} Tr (gΨ − z − m)^{-1} = m`, `Im m > 0` (p. 11).
- **Lean.** `BAbulk d L g κ E` is `κ ≤ BArho d L g E`, with `BArho d L g E = π^{-1} Im (BAm d L g E)`, where `BAm d L g E` at the real point is the solution of
  (2.32) at `z = E` with positive imaginary part if there is one, and `0` otherwise. `BASelf` is the block form `m = L^{-d} Tr (gΨ^{(B)} − z − m)^{-1}`.
- **Relation.** The traces agree: `Ψ = Ψ^{(B)} ⊗ I_{W^d}` gives `Tr = W^d Tr_block` and `N = W^d L^d`. In the bulk the real-axis solution is the boundary value:
  for `0 < κ ≤ ρ_N(E)`, `|π^{-1} Im m(E + iη) − ρ_N(E)| ≤ 2η/(π³κ²)` for all `η > 0` (`RBM.BA.BArho_rate_of_bulk`), and `κ ≤ ρ_N(E)` is equivalent to the existence of a
  solution at `z = E` with `π κ ≤ Im m` (`RBM.BA.BAbulk_iff_exists`). Conversely, if `π^{-1} Im m(E + iη) → ρ ≥ κ > 0`, a limit point of `m(E + iη)` (all have
  `|m| ≤ 1`, `RBM.BA.BAm_norm_le_one`) solves (2.32) at `z = E` with `Im m = πρ`, and the solution is unique (`RBM.BA.BASelf_unique`); this converse is a paper argument, not compiled.
  `B_κ` depends on `N` through `(L, g)`: Lean uses `BAbulk d (L n) (lam n) κ` at index `n`.

### 2.11 Universality for the block Anderson model, normalized by the local densities (identical as printed)

- **Paper** (p. 12, the display in Theorem 2.7): for fixed `n`, `O ∈ C_c^∞(ℝ^n)`, `E ∈ B_κ` and `E' ∈ (−2, 2)`,
  `lim_{N→∞} ∫ dα O(α)[ρ_N(E)^{-n} p_H^{(n)}(E + α_1/(Nρ_N(E)), …) − ρ_sc(E')^{-n} p_GUE^{(n)}(E' + α_1/(Nρ_sc(E')), …)] = 0`; for the band model `ρ_N = ρ_sc` and
  `E' = E` give (2.20) after `α ↦ ρ_sc(E)α`.
- **Lean.** `RBM.BA.BAEnd_BUnivL d` (Appendix A) is `UNUnivDilAt sz (UNModel.ba sz) (fun n => BArho d (L n) (lam n) E) E E' k O`: the expectations of
  `kPoint k (fun α => O (ρ_n • α)) E` for the eigenvalues of `sz.seqHBA n` under `Sizes.seqP (sz.withLam 0)`, with `ρ_n = ρ_N(E)` at index `n`, and of
  `kPoint k (fun α => O (rhoSC E' • α)) E'` for the GUE matrix, differ by `o(1)`; here `k ≥ 1`, `|E'| < 2`, and `E` satisfies `BAbulk d (L n) (lam n) κ E` for all large `n`.
- **Relation.** The substitution `α = ρβ` gives `ρ^{-k} ∫ O(α) p^{(k)}(E + α/(Nρ)) dα = ∫ O(ρβ) p^{(k)}(E + β/N) dβ`, so the paper's two terms are the two dilated
  expectations of `kPoint` (§2.9, §4.2). The hypothesis `E ∈ B_κ` is required in Lean only for large `n` (a weaker hypothesis, so the Lean statement is stronger).

### 2.12 The block Anderson matrices, local laws and quantum diffusion (identical)

- **Paper** (pp. 11-12; (2.33), (2.35), Definition 2.17 on p. 16): the results of Section 2.1 "remain valid" for `H = V + gΨ`, with `G` of (2.6), `m` of (2.32), `M` of (2.33) and the bulk (2.34);
  (2.22)-(2.25) hold with `|m|²Θ^{(+,−)}_{ab}` and `m²Θ^{(+,+)}_{ab}` replaced by `(Θ^{(+,−)}M^{(+,−)})_{ab}` and `(Θ^{(+,+)}M^{(+,+)})_{ab}`, where `M^{(σ₁,σ₂)}_{ab} = M^{(B)}_{ba}(σ₁)M^{(B)}_{ab}(σ₂)`
  and `Θ^{(σ₁,σ₂)} = (1 − M^{(σ₁,σ₂)}S^{(B)})^{-1}` with `S^{(B)} = I`.
- **Lean.** `BAThm27L d` is the conjunction `BAEnd_decolL d ∧ BAEnd_locSCL d ∧ BAEnd_QUEL d ∧ BAEnd_BUnivL d ∧ BAEnd_QDiffL d` (delocalization, local laws, QUE and universality, quantum diffusion;
  Appendix A) for the law `Sizes.seqP (sz.withLam 0)`, with `BAGz = Gres (sz.seqHBA n ω) z true`, `BAMz`, the domain `BAendDom κ ε n z` (`BAbulk … κ z.re ∧ N^{-1+ε} ≤ z.im ∧ z.im ≤ 1`) and the profile
  `BAprof n z σ₁ σ₂ a b = (Θ^{(σ₁,σ₂)} M^{(σ₁,σ₂)})_{ab}/W^d`, where `M^{(σ₁,σ₂)}` is `RBM.BA.BAMss` and `Θ^{(σ₁,σ₂)} = RBM.PropThetaQ M^{(σ₁,σ₂)} 1 = (1 − M^{(σ₁,σ₂)})^{-1}`. The events are those of
  §2.5-§2.8 with these substitutions; `(+, −)` is used for (2.22), (2.24) and `(+, +)` for (2.23), (2.25).

---

## 3. Uniformity in the size parameters

**The two forms.** In the paper the threshold for "`N` sufficiently large" depends only on the fixed constants (`d, 𝔠, 𝔡, κ, ε, τ, D`;
`ε₀, c` for Theorem 2.3; `k, E, O` for Theorem 2.4), not on `(W, L, g)`: the estimate holds for all triples `(W, L, g)` with `L ≥ 3`,
`W ≥ 1`, `N = (WL)^d ≥ N₀`, `W ≥ N^𝔠` and `W^{-d/2+𝔡} ≤ g ≤ 𝔡^{-1}`. The Lean statements say: for every size sequence `sz` with
`Admissible 𝔠 𝔡`, for all large `n`. The two forms are equivalent; the argument below is a paper argument and is not compiled.

**Uniform ⇒ Lean.** Let `sz.Admissible 𝔠 𝔡`. For large `n`, `N = sz.size n ≥ N₀`, `W n ≥ N^𝔠` and (2.10) holds, so `(W n, L n, lam n)` is one of
the triples of the uniform statement. The law of `sz.seqXmat n` under `Sizes.seqP sz` is the paper's law for this triple
(`RBM.Gauss.Sizes.seqP_map_slice`), and every event and quantity in the statements is a function of this matrix. Hence the bound holds for
large `n`.

**Lean ⇒ uniform.** Suppose that the uniform statement fails for some constants. Then for every `j` there is a triple `(W_j, L_j, g_j)` in the
admissible range with `N_j = (W_j L_j)^d ≥ j` at which the estimate fails (for some `z`, `E`, `a` or `A` where these occur). Put `sz.W j = W_j`,
`sz.L j = L_j`, `sz.lam j = g_j`. Then `sz.size j = N_j → ∞`, and `W_j ≥ N_j^𝔠` and (2.10) hold for every `j`, so `sz.Admissible 𝔠 𝔡`, and the
estimate fails at every index `j`, contradicting the Lean theorem. (No filler sequence is needed: a size sequence is arbitrary, and `sz.size n`
is exactly the matrix dimension.) For Theorem 2.4 the same gluing is applied to a subsequence on which the difference in (2.20) stays above some
`ε > 0`.

**The block Anderson model.** The coupling `g_n = lam n` enters the matrix `H = g_n Ψ + V`, the density `ρ_N` and the bulk `B_κ`, but not the law of `V`, which is that of
`sz.withLam 0` (its slice at `n` is `PF d (L n) (W n) 0`). The two arguments apply to the triples `(W_j, L_j, g_j)` without change; in the universality part the energy `E` is fixed and
`E ∈ B_κ` for `(L_j, g_j)` is required for large `j` only (§2.11), as in the Lean statement.

**Remark.** If `d𝔠 ≥ 1` or `𝔡 ≥ d/2`, no triple is admissible: in the first case `N^𝔠 = (WL)^{d𝔠} ≥ WL ≥ 3W > W`; in the second
`g ≥ W^{-d/2+𝔡} ≥ 1 > 2/d ≥ 𝔡^{-1} ≥ g`. So the theorems concern `0 < 𝔠 < 1/d` and `0 < 𝔡 < d/2`; for example `L ≡ 3` with `W → ∞` and `g_n` between
`W_n^{-d/2+𝔡}` and `𝔡^{-1}` is allowed.

---

## 4. The external input [LANDON20191137]

The paper uses one result from the literature that the Lean proof does not prove: [LANDON20191137, Theorem 2.2]. The PDF proves Theorem 2.4
(pp. 10-11) by adapting the proof of [28, Theorem 2.6], whose Step 1 applies it (in the form stated in arXiv:1609.09011v4, where the Remark
following Theorem 2.2 covers the complex Hermitian case). The Lean proof writes this step out for every `d ≥ 3`. In Lean the input is the hypothesis `RBM.Univ.UNL32` of `RBM.Endpoints.BUniv_of_L32`, `RBM.BA.baEnd_BUnivL_of_ML` and
`RBM.Endpoints.final_shape`.

### 4.1 The Lean statement

Namespace `RBM.Univ` (directory `RBM3D/Universality/`). `IsRegular32` is [LANDON20191137, Definition 2.1] (`mV` is the Stieltjes transform of `V`),
`IsFreeConv32` is its (2.5), `dbmMat d L W v t ω = diag(v) + √t · Xmat d L W ω` is its `H_t = V + √t W` with the GOE replaced by the GUE (`ω` under `gueP`), and `rhoSC` is its `ρ_sc` (2.4); `kPoint` is in §2.9
and Appendix A. The premises involve only `N = (W L)^d`; `d` enters through the carrier `Idx d L W` of the matrix. (In this section `g, G` are the parameters of [LANDON20191137], not the coupling of §1.)

```lean
def IsRegular32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (g G c C CV : ℝ) : Prop :=
  (∀ E η : ℝ, |E| ≤ G → g ≤ η → η ≤ 10 →
      c ≤ (mV v ⟨E, η⟩).im ∧ (mV v ⟨E, η⟩).im ≤ C) ∧
    ∀ i, |v i| ≤ (Fintype.card ι : ℝ) ^ CV
def IsFreeConv32 {ι : Type*} [Fintype ι] (v : ι → ℝ) (t : ℝ) (m : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 < (m z).im ∧
    m z = (Fintype.card ι : ℂ)⁻¹ * ∑ i, ((v i : ℂ) - z - (t : ℂ) * m z)⁻¹
def UNL32 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
  ∀ (δ σ q c C CV : ℝ), 0 < δ → 0 < σ → 0 < q → q < 1 → 0 < c →
  ∀ (g G t E : ℕ → ℝ) (v : ∀ n, Idx d (sz.L n) (sz.W n) → ℝ) (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ),
    (∀ᶠ n in atTop,
      ((sz.size n : ℕ) : ℝ) ^ δ / ((sz.size n : ℕ) : ℝ) ≤ g n ∧
      g n ≤ ((sz.size n : ℕ) : ℝ) ^ (-δ) ∧ G n ≤ ((sz.size n : ℕ) : ℝ) ^ (-δ) ∧
      g n * ((sz.size n : ℕ) : ℝ) ^ σ ≤ t n ∧ t n ≤ ((sz.size n : ℕ) : ℝ) ^ (-σ) * G n ^ 2 ∧
      |E n| ≤ q * G n ∧
      IsRegular32 (v n) (g n) (G n) c C CV ∧ IsFreeConv32 (v n) (t n) (m n) ∧
      Tendsto (fun η : ℝ => (m n ⟨E n, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 (ρ n))) →
    ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
      Tendsto (fun n =>
        (∫ ω, kPoint k (fun α => O (ρ n • α)) (E n)
            (dbmMat_isHermitian d (sz.L n) (sz.W n) (v n) (t n) ω).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))) -
        (∫ ω, kPoint k (fun α => O (rhoSC (E n) • α)) (E n)
            (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))))
        atTop (𝓝 0)
```

In words: along a size sequence with `N → ∞`, if for large `n` the diagonal matrix `diag(v n)` is `(g, G)`-regular, `g N^σ ≤ t ≤ N^{-σ}G²`, `|E| ≤ qG`, `m n` solves (2.5) and `ρ n` is the
density (2.6) (the limit of `π^{-1} Im m(E + iη)` as `η ↓ 0`), then the two dilated `k`-point functionals differ by `o(1)`.

### 4.2 How it matches [LANDON20191137, Theorem 2.2] in the form of arXiv:1609.09011v4

[LANDON20191137] considers `H_t = V + √t W` with `V` a deterministic diagonal matrix and `W` a GOE matrix. Its (2.7) is
`p^{(k)}_{H_t}(λ_1,…,λ_k) = ∫ p^{(N)}_{H_t}(λ_1,…,λ_N) dλ_{k+1}⋯dλ_N`, where `p^{(N)}_{H_t}` is the symmetrized eigenvalue probability density. Theorem 2.2:
if `V` is `(g, G)`-regular (Definition 2.1), `g N^σ ≤ t ≤ N^{-σ}G²` (2.8) and `|E| ≤ qG`, then there is `κ > 0` such that for every `k` and `O ∈ C_c^∞(ℝ^k)` there is `C > 0` with

```
| ρ_{fc,t}(E)^{-k} ∫ O(α) p^{(k)}_{H_t}(E + α/(Nρ_{fc,t}(E))) dα
  − ρ_{sc}(E)^{-k} ∫ O(α) p^{(k)}_{GOE}(E + α/(Nρ_{sc}(E))) dα | ≤ C N^{-κ}.        (2.9)
```

- **The density factors.** In arXiv:1609.09011v4 the two integrals of (2.9) carry the prefactors `ρ_{fc,t}(E)^{-k}` and `ρ_{sc}(E)^{-k}`; the earlier version
  arXiv:1609.09011v3 has none. The substitution `α = ρβ` gives `ρ^{-k} ∫ O(α) p^{(k)}(E + α/(Nρ)) dα = ∫ O(ρβ) p^{(k)}(E + β/N) dβ`: each side's test function is
  dilated by that side's own density. This is the form of `UNL32`, in the eigenvalue-sum form `kPoint` (§2.9): `kPoint k (fun α => O (ρ n • α)) (E n)` on the first side and
  `kPoint k (fun α => O (rhoSC (E n) • α)) (E n)` on the second.
- **The complex Hermitian case.** [LANDON20191137] states and proves its results for the real symmetric case. The Remark after Theorem 2.2 in arXiv:1609.09011v4 states that the
  methods and results hold also for the complex Hermitian case, with essentially only notational changes. `UNL32` is the statement for the complex Hermitian case: `dbmMat` is
  `V + √t X` with `X = RBM.Gauss.Xmat` under the GUE law `RBM.Univ.gueP` (§2.9), and the comparison matrix is a GUE matrix.

### 4.3 The two ways `UNL32` is weaker than [LANDON20191137, Theorem 2.2]

1. **Along size sequences.** `UNL32` is a statement for each size sequence, with the premises required for large `n` only and fixed `δ, σ, q, c, C, C_V, k, O`.
   [LANDON20191137, Theorem 2.2] gives, for these fixed parameters, one `C` and one `κ` for every `N`, `V`, `t`, `E` satisfying the premises (the standard reading of the
   theorem).
2. **The rate.** The bound `C N^{-κ}` is weakened to "tends to `0`".

### 4.4 The places where `UNL32` is used

Both are in Step 1 of the proof of Theorem 2.4 (as in [28, Theorem 2.6]), written out for the band model and in the same form for the block Anderson model, whose
flow is centred at `gΨ` (the universality part of Theorem 2.7; p. 72).

1. **The model matrix.** The matrix `𝐇_{t*} = e^{-t*/2}H + √(1−e^{-t*})H'` (`RBM.Univ.ouMat`, `t* = N^{-1+τ_U}`, `H'` an independent GUE matrix) has, conditionally on
   `H`, the eigenvalue statistics of `dbmMat` started from the diagonal matrix of the eigenvalues of `e^{-t*/2}H − E` and run for time `1 − e^{-t*}`
   (`RBM.Univ.step1Band_integral_ouP`); `UNL32` is applied at energy `0`. The initial data is `(g, G)`-regular with probability `1 − N^{-D}`, by the local law, with
   `g = N^{-1+τ_U/4}`, `G = N^{-min(τ_U/4,(1−τ_U)/3)}`, `τ_U ≤ 𝔠𝔡`, and the density of the free convolution at `0` is within `N^{-3τ_U/8}` of `ρ_n`
   (`RBM.Univ.step1Good'`). This is `RBM.Univ.step1Band` for the band model and `RBM.Univ.step1BandC''` for the centred flow of the block Anderson model.
2. **The translation of the GUE from energy 0 to energy `E`.** The same argument compares the GUE statistics near `E` with those near `0`: `RBM.Univ.guetranslation`,
   whose regularity premise comes from the GUE local law, proved in Lean (§5.7).

---

## 5. Where the Lean proof takes a different route

None of the items below changes a statement of §1. For each item: the paper's step, the Lean replacement and the main declarations. In `RBM3D/`, the
directories `Gauss` and `Path` hold the probability space, the one-time flow and the grid walk (the flow framework, Section 2.3); `Loop` the `G`-loops and
`𝒦`-loops (Sections 2.3-2.4, Appendix A.5); `Propagator` and `Kernel` Lemma 2.19 and Appendix A; `Green`, `Evolution`, `Induction` and `Chain` Sections 3-6
(Steps 1-6); `Graph` Section 7 and Appendix B; `BA` the block Anderson model (Section 8 and the corresponding parts of Sections 3-7 and the appendices); `Universality` the proof of Theorem 2.4; and `Main` the assembly of Theorems 2.1-2.5. Many
deterministic lemmas are proved with explicit constants where the paper writes `O(·)`, `≍` or `≺`, and implicit conditions are hypotheses.

### 5.1 The Brownian flow (pp. 12-13)

- **Paper.** The matrix Brownian motion `H_t` (2.36), `H_0 = 0` (band) or `gΨ` (block Anderson); the spectral parameter `z_t` (2.37), (2.38); and Lemma 2.10 (2.43):
  `G(z) =_d √t₀ G_{t₀;E}` with `t₀ = |m(z)|²`, `E = −2 Re m(z)/|m(z)|` (2.42).
- **Lean.** Two models with the paper's one-time laws. `RBM.Gauss.Sizes.seqHflow sz n u ω = √u · seqXmat sz n ω` has the right law at each time and is not a Brownian path; it turns
  (2.43) into a pointwise identity (`RBM.Gauss.Sizes.Gt_lemT`, `RBM.Endpoints.zGreen`, with `t₀ = RBM.lemT z`, `E = RBM.lemE z`); the block Anderson flow is `seqHflowBA` and
  (8.2) is `RBM.Gauss.Sizes.Gt_BA`. The grid walk `RBM.Path.pathH`, for a grid `u_k = s + kΔ`, is `H_{u_k} = √s X_0 + √Δ ∑_{i=1}^k X_i` with independent copies `X_i` of the band matrix,
  on `RBM.Path.pathP` with the filtration `RBM.Path.filt`; `RBM.Path.transferLaw` says that its law at step `k` is the law of `seqHflow` at time `u_k`. Arguments that need several
  times (stopping times, martingale bounds) are carried out on this walk.

### 5.2 From the Itô formula to Gaussian integration by parts

- **Paper.** The loop hierarchy (2.47) (p. 14) is derived by Itô's formula (p. 14; the same derivation is applied to twisted loops on p. 78). Gaussian integration by parts is used for the light-weight terms (pp. 24, 55).
- **Lean.** At one time, the derivative in `u` of an expected loop is the expectation of a finite sum of cut loops (`RBM.Gauss.deriv_integral_gloop_eq_integral_samplewiseLoopGeneratorCuts`); the
  second-order terms come from Stein's identity `E[x f(x)] = v E[f'(x)]` for each real coordinate (`RBM.integral_mul_gaussianReal`). Along the walk, `RBM.Path.oneStepEnvelope` says that for Hermitian
  `M`, `|E| < 2`, `0 ≤ u`, `0 ≤ Δ`, `u + Δ < 1` and a loop of length `k`, `‖E Φ_{u+Δ}(M + √Δ X) − Φ_u(M) − Δ·genMat‖ ≤ envConst · Δ^{3/2}`, where `RBM.Path.genMat` is `½ ∑_c gvar_c ∂_c² Φ_u + ∂_u Φ_u`
  (the generator that the Itô formula produces) and `RBM.Path.envConst` is `16(k+3)^4 N^4 (1 + η_v^{-1})^{k+4}`.

### 5.3 Martingale terms: Azuma-Hoeffding in place of Burkholder-Davis-Gundy

- **Paper.** The martingale term of the integrated hierarchy (3.13) is bounded by the Burkholder-Davis-Gundy type Lemma 3.6 ((3.17), (3.18), p. 22, from [69]), for stopping times of `{H_t}`.
- **Lean.** On the grid, the linear part of the one-step martingale increment is conditionally sub-Gaussian (`RBM.Path.hasCondSubgaussianMGF_linear`), and the stopped sums are
  bounded by the Azuma-Hoeffding inequality (`RBM.Path.azuma_two_sided`, `RBM.Path.azuma_complex`) and Doob's maximal inequality (`RBM.Path.doob_L2_max`); the stopped first-chaos
  increments are conditionally sub-Gaussian (`RBM.Ind.azumaSubGN`).

### 5.4 Stopping times, nets, the relation `≺`

- **Paper.** Stopping times for `{H_t}` (Lemma 3.4, p. 21; (3.49), p. 25); uniformity in time by "a standard `N^{-C}`-net argument"; the relation `≺` of (1.13) (p. 6).
- **Lean.** Stopping times are first hitting indices of the grid: `RBM.Path.firstHit` (a stopping time: `RBM.Path.isStoppingTime_firstHit`). Bounds uniform in time follow from bounds
  at each time by explicit polynomial nets (`RBM.Gauss.netSize`, `RBM.Gauss.netPt`, `RBM.Gauss.exists_netPt_close`) and a union bound. The relation `≺` is `RBM.StochDomAt` along the
  dimensions `size n`. Moment bounds (`RBM.Gauss.MomentDomAt`) give `≺` by Markov's inequality (`RBM.Gauss.stochDomAt_of_momentDomAt`); the reverse (`RBM.Gauss.momentDomAt_of_stochDomAt`)
  uses the whole-space bound `‖G(z)‖ ≤ (Im z)^{-1}`.

### 5.5 The loops `𝒦`

- **Paper.** `𝒦` is "the unique solution" of the convolution tree equations (2.50) with the initial data (2.52) (Definition 2.14, p. 14; (2.52) is on p. 15), and has an explicit tree representation (Appendix A.5, p. 86, (A.30), p. 87).
- **Lean.** `RBM.Loop.KLK` is defined by the tree sum, and `RBM.Loop.KLK_isKLoop` shows that it solves (2.50) on `[0, 1)` with the initial data and `𝒦^{(1)} = m(σ)`; the uniqueness of the solution, which
  the paper's definition presupposes, is not used by the Lean proof. The Ward identity (2.57) is `RBM.Loop.wardS_holds`.

### 5.6 The propagator `Θ` (Lemma 2.19, Appendix A.1)

- **Paper.** Properties 5-8 "have essentially been established in previous works" (p. 16): Fourier series and summation by parts for `σ₁ ≠ σ₂`, the shifted Taylor expansion (A.2) for `σ₁ = σ₂`, random-walk bounds.
- **Lean.** For `σ₁ ≠ σ₂`, `Θ_t(0, a) = γ^{-1}∫₀^∞ e^{-ετ} K_τ(a) dτ` (`RBM.Heat.Theta_eq_laplace_prod`), with `K_τ` the product of one-dimensional heat kernels of the torus, `ε = (1−t)/γ`; the decay and
  the zero-mode estimate follow from Laplace-Gauss bounds (`RBM.prop5Decay_holds`, `RBM.prop8ZeroMode_holds`), the first and second differences from the unit differences by a path argument
  (`RBM.prop6Diff1_holds`, `RBM.prop7Diff2_holds`). For `σ₁ = σ₂`, `RBM.prop5Short_holds` uses the gap and a Neumann series. For the block Anderson model `RBM.BA.baProp5to8_holds`
  treats `σ₁ ≠ σ₂` by the same representation with the kernel of `M^{(σ₁,σ₂)}`, and `σ₁ = σ₂` by a weighted `ℓ^∞` (Combes-Thomas) estimate in place of the Neumann series. The constants depend only on
  `(d, Λ)`, resp. `(d, Λ, κ)`, with `0 < g ≤ Λ`, fixed before `L, g, t`.

### 5.7 Statements that the paper takes from the literature or omits, proved in Lean

| Paper | Lean |
|---|---|
| Lemma 2.15, Ward identities for `𝒦` (corresponding to Lemma 3.6 in [69] and Lemma 3.17 in [59], p. 15) | `RBM.Loop.wardS_holds` (§5.5) |
| Lemma 2.19 (p. 16) | `RBM.prop5to8_holds`; `RBM.BA.baProp5to8_holds` (§5.6) |
| Lemma 3.1 (`lem_GbEXP`), proved as Lemma 4.1 of [69] for `d = 1` (p. 19) | `RBM.Green.gbEXPV3` |
| Lemma 3.2 (`lem_ConArg`), proved exactly as Lemma 5.1 of [69] (p. 20) | `RBM.Ind.conArg` |
| Theorem 2.24 (the main induction, Steps 1-6, p. 18), which gives the loop estimates of Lemmas 2.21-2.23 (p. 17) | `RBM.Univ.unMLOut_holds` (the loop estimates along every flow, for every `d ≥ 3`); for the block Anderson model `RBM.BA.baMainIndFamTL_any` (§5.9) |
| Theorem 2.1, which follows directly from (2.14) (p. 8) | `RBM.Endpoints.decol_of_locSC` (§5.8) |
| Theorem 2.3, proved similarly to [69, Theorem 2.5], [28, Theorem 2.4] and [59, Theorem 2.2] (p. 10) | `RBM.Endpoints.QUE_of_QDiff` (§5.8) |
| Theorem 2.4, which follows from the Green function comparison method of [64] and the proof of [28, Theorem 2.6] (p. 10) | Step 1 and the translation of the GUE (§4.4); `RBM.Univ.greenCorrAll` (comparison of the `k`-point functionals through Poisson smoothing); `RBM.Univ.unEMCTE2Row`, `RBM.Univ.jakUywRow`; `RBM.Endpoints.unOURow`; assembled in `RBM.Endpoints.bUniv_holds` |
| The GUE local law used in Step 1 | `RBM.Univ.un_gueLocal_of_tail` applied to `RBM.Univ.gueSchurTail` |

The GUE local law is proved from the Schur complement formula (`RBM.Univ.gueSchurTail`) with a deterministic bootstrap (`RBM.Univ.un_gueLocal_of_tail`). The processes of Step 1 are used only through their one-time laws
`𝐇_t = e^{-t/2}H + √(1−e^{-t})H'` with `H'` an independent GUE matrix (`RBM.Univ.ouMat`, on the carrier `RBM.Univ.ouP`); the generator identity for `𝔼Φ(𝐇_t)` is
`RBM.Univ.ouGenerator_hasDerivAt_integral`.

### 5.8 The deductions of Theorems 2.1 and 2.3

- **Theorem 2.1** (`RBM.Endpoints.decol_of_locSC`). The paper applies the local law (2.14) at `η = N^{-1+τ}` and (2.16). Lean uses `η = N^{-1+ε}`, `ε = min(τ/2, 1/2)`, so that the constant in
  `|ψ_k(x)|² ≤ η Im G_xx(λ_k + iη)` is absorbed: with `|G_xx − m| ≤ 1` and `Im m ≤ 1`, `|ψ_k(x)|² ≤ 2η ≤ N^{-1+τ}` for large `n` (the carrier-free core is `RBM.Endpoints.decol_spectral_core`).
- **Theorem 2.3** (`RBM.Endpoints.QUE_of_QDiff`). Only the expectation half (2.24), (2.25) of Theorem 2.5 is used, at the single spectral parameter `z = E + iη_Q` with
  `η_Q = W^{-ε₀}(g W^{d/2}/N)` as in the paper (p. 10), with `(κ, ε, τ, D) = (κ, 𝔠(𝔡 − ε₀), τ/2, 1)`. The differences of the profile between blocks are bounded by `C g^{-2} W^{-d}` with `C = C(d, 𝔡, κ)`
  (`RBM.Endpoints.queRowDiff`; the paper writes `≺ g^{-2}` after (2.28)). Both (2.18) and (2.19) follow from Markov's inequality.

### 5.9 The block Anderson model: one chain over a flow carrier, in family form

- **Paper.** Section 8 describes the block Anderson case as changes to Sections 3-7 (p. 71); Theorem 2.7 is proved from Theorem 8.2 (p. 72) by "induction on `t` from `t = 0` to `t = t₀` (simultaneously for all
  target spectral parameters".
- **Lean.** The generic steps are stated over a flow carrier `RBM.BA.FlowFM` and instantiated at the band model (`RBM.BA.bandFM`) and at the block Anderson tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz,
  BAflowT0)`. The induction step is stated for every member `z'` of a family `Fam(t)` of flows at once (`RBM.BA.BAMainIndFamTL d R`, `RBM.BA.BAFamZ`); its terminal form
  is `RBM.BA.baMainIndFamTL_any`, which gives the step at every `d ≥ 3` from Step 5 (iii) (`RBM.BA.baStep5III_holds_any`), and `RBM.BA.unMLOutBA_of_famStep` turns it into the loop estimates
  `UNMLOutBA d`.

---

## Appendix A. The Lean statements

The five band statements and the definitions they use (namespace `RBM.Endpoints`, file `RBM3D/Endpoints.lean`); then the block Anderson end statements (namespace `RBM.BA`, files `RBM3D/BA/MAPins.lean`
and `RBM3D/BA/UNPins.lean`). In the definitions below `d` is an implicit argument and `sz : Sizes d`; `Nsz sz n` is `N = sz.size n` as a real number; `calB`, `distB`, `Mband`, `Gn`, `Theta` are described in §2.7 and §2.8, `kPoint`, `gueP`, `gueVar`, `IsTestFun` in §2.9, `BAGz` and `BAMz` (`G` and `M` of the block Anderson model) in §2.12.

```lean
-- namespace RBM.Univ (RBM3D/Universality/Pins.lean)
def IsOrthoEigenbasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ) : Prop :=
  (∀ k k', star (ψ k) ⬝ᵥ ψ k' = if k = k' then 1 else 0) ∧
    ∀ k, H *ᵥ ψ k = (μ k : ℂ) • ψ k
def kPoint {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) (E : ℝ) (lam : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) ^ k / ((Fintype.card ι).descFactorial k : ℝ)) *
    ∑ f : Fin k ↪ ι, O (fun j => (Fintype.card ι : ℝ) * (lam (f j) - E))
def gueVar (d L W : ℕ) (c : CoordF d L W) : ℝ≥0 :=
  if c.1 = c.2.1 then ((((W * L) ^ d : ℕ) : ℝ≥0))⁻¹ else ((2 * ((W * L) ^ d : ℕ) : ℝ≥0))⁻¹
def gueP (d L W : ℕ) [NeZero L] [NeZero W] : Measure (Ω d L W) :=
  Measure.infinitePi fun c => gaussianReal 0 (gueVar d L W c)
def queWindow (d L W : ℕ) (lam ε₀ E x : ℝ) : Prop :=
  |x - E| ≤ (W : ℝ) ^ (-ε₀) * (lam * (W : ℝ) ^ ((d : ℝ) / 2) / (((W * L) ^ d : ℕ) : ℝ))
def queBound (W : ℕ) (𝔡 ε₀ c τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((W : ℝ) ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ))
def queBadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (a : Zd d L)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ i j, queWindow d L W lam ε₀ E (μ i) ∧ queWindow d L W lam ε₀ E (μ j) ∧
      (W : ℝ) ^ ((d : ℝ) - c) / (((W * L) ^ d : ℕ) : ℝ) ≤
        ‖(∑ x ∈ Iblk d L W a, star (ψ i x) * ψ j x) -
            ((W : ℂ) ^ d / (((W * L) ^ d : ℕ) : ℂ)) * (if i = j then 1 else 0)‖
def UNBUniv : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
        Tendsto (fun n =>
          (∫ ω, kPoint k O E (Sizes.seqXmat_isHermitian sz n ω).eigenvalues ∂(Sizes.seqP sz)) -
          (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
            ∂(gueP d (sz.L n) (sz.W n))))
          atTop (𝓝 0)
def UNUnivDilAt (sz : Sizes d) (M : UNModel sz) (ρ : ℕ → ℝ) (E E' : ℝ) (k : ℕ)
    (O : (Fin k → ℝ) → ℝ) : Prop :=
  Tendsto (fun n =>
    (∫ ω, kPoint k (fun α => O (ρ n • α)) E (M.herm n ω).eigenvalues ∂M.μ) -
    (∫ ω, kPoint k (fun α => O (rhoSC E' • α)) E' (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
      ∂(gueP d (sz.L n) (sz.W n)))) atTop (𝓝 0)
-- namespace RBM.Endpoints (RBM3D/Endpoints.lean)
def calB (sz : Sizes d) (n : ℕ) (η K : ℝ) : ℝ :=
  (sz.lam n ^ 2 + η)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (K + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) +
    (((sz.size n : ℕ) : ℝ) * η)⁻¹
def distB (sz : Sizes d) (n : ℕ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)
def Mband (sz : Sizes d) (n : ℕ) (z : ℂ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  if x = y then msc z else 0
def avg2 (sz : Sizes d) (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (a b : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) b, F x y
def ThetaPM (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (((‖msc z‖ ^ 2 : ℝ)) : ℂ)
def ThetaPP (sz : Sizes d) (n : ℕ) (z : ℂ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Theta d (sz.L n) (sz.lam n) (msc z ^ 2)
def profPM (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  (((‖msc z‖ ^ 2 : ℝ)) : ℂ) * ThetaPM sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d
def profPP (sz : Sizes d) (n : ℕ) (z : ℂ) (a b : Zd d (sz.L n)) : ℂ :=
  msc z ^ 2 * ThetaPP sz n z a b / ((sz.W n : ℕ) : ℂ) ^ d
def qdBound (sz : Sizes d) (n : ℕ) (τ η : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * min (calB sz n η 0 ^ ((1 : ℝ) / 5) * calB sz n η (distB sz n a b))
    (calB sz n η 0 ^ 2)
def qdBoundExp (sz : Sizes d) (n : ℕ) (τ η : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n η 0 ^ 2 *
    ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 : ℝ) / 5) + calB sz n η 0)
def decolBad (sz : Sizes d) (n : ℕ) (κ τ : ℝ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqXmat n ω) μ ψ → ∀ k, |μ k| ≤ 2 - κ → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)
def locBad1z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n),
    ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
      ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2
def locBad2z (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x - msc z‖
def qd1Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b - profPM sz n z a b‖
def qd2Badz (sz : Sizes d) (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b - profPP sz n z a b‖
def locBad1 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad1z sz τ n z ω
def locBad2 (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ locBad2z sz τ n z ω
def qd1Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd1Badz sz τ n z ω
def qd2Bad (sz : Sizes d) (κ ε τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ∃ z : ℂ, sz.locDomain κ ε n z ∧ qd2Badz sz τ n z ω
def que2BadMat (d L W : ℕ) [NeZero L] [NeZero W] (lam ε₀ c E : ℝ) (A : Finset (Zd d L))
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Prop :=
  ∃ (μ : Idx d L W → ℝ) (ψ : Idx d L W → Idx d L W → ℂ),
    IsOrthoEigenbasis M μ ψ ∧ ∃ k, queWindow d L W lam ε₀ E (μ k) ∧
      (W : ℝ) ^ ((d : ℝ) - c) * (A.card : ℝ) / (((W * L) ^ d : ℕ) : ℝ) ≤
        |(∑ a ∈ A, ∑ x ∈ Iblk d L W a, ‖ψ k x‖ ^ 2) -
            (W : ℝ) ^ d / (((W * L) ^ d : ℕ) : ℝ) * (A.card : ℝ)|
def decol : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | decolBad sz n κ τ ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
def locSC : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | locBad1 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP sz {ω | locBad2 sz κ ε τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
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
abbrev BUniv : Prop := UNBUniv
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
-- namespace RBM.BA (RBM3D/BA/MAPins.lean, RBM3D/BA/UNPins.lean): Theorem 2.7 at dimension d
def BAprof (n : ℕ) (z : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)) : ℂ :=
  (PropThetaQ (BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) σ₁ σ₂) 1 *
    BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) σ₁ σ₂) a b /
      ((sz.W n : ℕ) : ℂ) ^ d
def BAendDom (κ ε : ℝ) (n : ℕ) (z : ℂ) : Prop :=
  BAbulk d (sz.L n) (sz.lam n) κ z.re ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1
def BAlocBad1z (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ x y : Idx d (sz.L n) (sz.W n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im (distB sz n (STblk sz n x) (STblk sz n y)) <
    ‖BAGz sz n z ω x y - BAMz sz n z x y‖ ^ 2
def BAlocBad2z (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) : Prop :=
  ∃ a : Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ τ * calB sz n z.im 0 <
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, BAGz sz n z ω x x - BAm d (sz.L n) (sz.lam n) z‖
def BAqdBadz (τ : ℝ) (n : ℕ) (z : ℂ) (ω : sz.SeqΩ) (σ : Bool) : Prop :=
  ∃ a b : Zd d (sz.L n), qdBound sz n τ z.im a b <
    ‖avg2 sz n (fun x y => if σ then BAGz sz n z ω x y * BAGz sz n z ω y x else ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b -
      BAprof sz n z true σ a b‖
def BAdecolBad (κ τ : ℝ) (n : ℕ) (ω : sz.SeqΩ) : Prop :=
  ¬ ∀ (μ : Idx d (sz.L n) (sz.W n) → ℝ) (ψ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
    IsOrthoEigenbasis (sz.seqHBA n ω) μ ψ → ∀ k, BAbulk d (sz.L n) (sz.lam n) κ (μ k) → ∀ x,
      ‖ψ k x‖ ^ 2 ≤ Nsz sz n ^ (-1 + τ)
def BAEnd_decolL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ τ D : ℝ, 0 < κ → 0 < τ → 0 < D →
    ∀ᶠ n in atTop, Sizes.seqP (sz.withLam 0) {ω | BAdecolBad sz κ τ n ω} ≤ ENNReal.ofReal (Nsz sz n ^ (-D))
def BAEnd_locSCL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad1z sz τ n z ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
      Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad2z sz τ n z ω} ≤
        ENNReal.ofReal (Nsz sz n ^ (-D))
def BAqueConclL {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) (𝔡 κ ε₀ c τ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ E : ℝ, BAbulk d (sz.L n) (sz.lam n) κ E →
    (∀ a : Zd d (sz.L n),
      μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqHBA n ω)} ≤
        queBound (sz.W n) 𝔡 ε₀ c τ) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      μ {ω | RBM.Endpoints.que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqHBA n ω)} ≤
        queBound (sz.W n) 𝔡 ε₀ c τ)
def BAEnd_QUEL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      BAqueConclL sz (Sizes.seqP (sz.withLam 0)) 𝔡 κ ε₀ c τ
def BAEnd_BUnivL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ k : ℕ, 1 ≤ k → ∀ κ : ℝ, 0 < κ →
    ∀ E : ℝ, (∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) κ E) → ∀ E' : ℝ, |E'| < 2 →
      ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
        UNUnivDilAt sz (UNModel.ba sz) (fun n => BArho d (sz.L n) (sz.lam n) E) E E' k O
def BAEnd_QDiffL (d : ℕ) : Prop :=
  3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ ε τ D : ℝ, 0 < κ → 0 < ε → 0 < τ → 0 < D →
    ∀ᶠ n in atTop,
      (Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAqdBadz sz τ n z ω false} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D)) ∧
        Sizes.seqP (sz.withLam 0) {ω | ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAqdBadz sz τ n z ω true} ≤
          ENNReal.ofReal (Nsz sz n ^ (-D))) ∧
      ∀ z : ℂ, BAendDom sz κ ε n z → ∀ a b : Zd d (sz.L n),
        ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z true false a b‖ ≤ qdBoundExp sz n τ z.im ∧
        ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n z ω x y * BAGz sz n z ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) -
            BAprof sz n z true true a b‖ ≤ qdBoundExp sz n τ z.im
def BAThm27L (d : ℕ) : Prop :=
  BAEnd_decolL d ∧ BAEnd_locSCL d ∧ BAEnd_QUEL d ∧ BAEnd_BUnivL d ∧ BAEnd_QDiffL d
```
