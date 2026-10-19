# Lean formalization of Dubova–Yang–Yau–Yin, "Delocalization of non-mean-field random matrices in dimensions d ≥ 3"

This repository contains a Lean 4 / Mathlib proof of the main results of

> Sofiia Dubova, Fan Yang, Horng-Tzer Yau and Jun Yin, *Delocalization of non-mean-field random matrices in
> dimensions d ≥ 3*, [arXiv:2507.20274](https://arxiv.org/abs/2507.20274).

The version of the paper that the Lean code follows is
[`paper/DubovaYangYauYin_RBM3D_Lean_version.pdf`](paper/DubovaYangYauYin_RBM3D_Lean_version.pdf)
(LaTeX source in `paper/tex/`). Page, equation and theorem numbers in `docs/PAPER-VS-LEAN.md` refer to this PDF.

Sister projects: [RBM1D](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718), the Lean proof of Yau–Yin,
*Delocalization of one-dimensional random band matrices* (arXiv:2501.01718), and
[RBM2D](https://github.com/JYin80/Lean-RBM2d_arxiv-2503.07606), the Lean proof of Dubova–Yang–Yau–Yin,
*Delocalization of two-dimensional random band matrices* (arXiv:2503.07606).

## Main results

All six results are proved for every dimension `d ≥ 3`, as stated in the paper. The statements for the random band
matrix model are closed propositions in [`RBM3D/Endpoints.lean`](RBM3D/Endpoints.lean); Theorem 2.7, for the block
Anderson model, is `RBM.Endpoints.Thm27 := ∀ d, 3 ≤ d → RBM.BA.BAThm27L d`
([`RBM3D/Main/FinalShape.lean`](RBM3D/Main/FinalShape.lean); `RBM.BA.BAThm27L` is stated in
[`RBM3D/BA/MAPins.lean`](RBM3D/BA/MAPins.lean)). The final theorem is

```lean
theorem RBM.Endpoints.final_shape :
    RBM.Univ.UNL32 →
      (decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff) ∧ Thm27
```

in [`RBM3D/Main/FinalShape.lean`](RBM3D/Main/FinalShape.lean).

| Paper | Lean statement | Lean theorem | What it says |
|---|---|---|---|
| Theorem 2.1 | `RBM.Endpoints.decol` | `RBM.Endpoints.decol_holds` | Delocalization: with probability at least `1 − N^{−D}`, every eigenvector whose eigenvalue lies in `[−2+κ, 2−κ]` satisfies `‖ψ_k‖²_∞ ≤ N^{−1+τ}`. |
| Theorem 2.2 | `RBM.Endpoints.locSC` | `RBM.Endpoints.locSC_holds` | Local law: the entrywise bound (2.14) and the block-averaged bound (2.15), each with probability at least `1 − N^{−D}`, uniformly in `z ∈ 𝐃_{κ,ε}`. |
| Theorem 2.3 | `RBM.Endpoints.QUE` | `RBM.Endpoints.QUE_holds` | Quantum unique ergodicity, (2.18) and (2.19). |
| Theorem 2.4 | `RBM.Endpoints.BUniv` | `RBM.Endpoints.BUniv_of_L32` | Bulk universality, (2.20), from the external input `UNL32`. |
| Theorem 2.5 | `RBM.Endpoints.QDiff` | `RBM.Endpoints.QDiff_holds` | Quantum diffusion, (2.22)–(2.25). |
| Theorem 2.7 | `RBM.Endpoints.Thm27` | `RBM.Endpoints.Thm27_of_L32` | The block Anderson model `H = V + gΨ`: delocalization, local law, QUE and quantum diffusion in the bulk `B_κ` of the density `ρ_N`, and bulk universality normalized by the local densities, from `UNL32`. |

Theorems 2.1, 2.2, 2.3 and 2.5 have no hypotheses other than their parameters. Theorems 2.4 and 2.7 have one more
hypothesis, `RBM.Univ.UNL32`, described below. `docs/PAPER-VS-LEAN.md` lists every difference between a Lean
statement and the printed one (for example, the statements are made along any admissible sequence of sizes, which is
the paper's "for `N` sufficiently large").

## The models and the one external input

The band matrix is the Gaussian block band matrix of the paper's §2.1 on the torus `Z_{WL}^d`: `L^d` blocks of size
`W^d`, `N = (WL)^d`, entries independent up to Hermitian symmetry, with variance profile `S_xy = W^{−d} S^{(B)}_{ab}`,
where `S^{(B)}(g)` of (2.5) has weight `(1+2dg²)^{−1}` on the diagonal and `g²(1+2dg²)^{−1}` on the `2d` nearest
neighbours of the block lattice, under the size conditions (2.9), (2.10). The block Anderson model of §2.2 is
`H = V + gΨ` with `V` the block-diagonal Gaussian potential and `Ψ = Ψ^{(B)} ⊗ I_{W^d}`.

The proof uses exactly one result from the literature without proving it: the fixed-energy universality of Dyson
Brownian motion (B. Landon, P. Sosoe, H.-T. Yau, *Fixed energy universality of Dyson Brownian motion*, Adv. Math.
346 (2019), Theorem 2.2, in the form stated in [arXiv:1609.09011v4](https://arxiv.org/abs/1609.09011v4), whose Remark
after Theorem 2.2 covers the complex Hermitian case). It enters only the universality statements (Theorem 2.4 and the
universality part of Theorem 2.7), as the explicit hypothesis `RBM.Univ.UNL32` (stated in
`RBM3D/Universality/Pins.lean`). `docs/PAPER-VS-LEAN.md` §4 states it and explains how it is used. The other results
that the paper quotes from earlier work are proved in Lean (`docs/PAPER-VS-LEAN.md` §5).

## Axioms

Every declaration of the library depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There is
no `sorry` and no declared `axiom`. The last command of `RBM3D.lean`, `#assert_rbm_axioms` (defined in
`RBM3D/Test/Axioms.lean`), checks this for every declaration in the namespace `RBM`, and makes the build fail
otherwise.

## Build

The toolchain is `leanprover/lean4:v4.34.0` (file `lean-toolchain`) with Mathlib `v4.34.0`.

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; `lake build` builds the whole library, including the axiom check
above.

The hypotheses of the theorems can be satisfied: compiled examples in `RBM3D/Main/BandTerminal.lean`,
`RBM3D/Main/FinalShape.lean`, `RBM3D/Main/BUnivHolds.lean` and `RBM3D/BA/MAPins.lean` apply them to explicit size
sequences (at `d = 3`, and at `d = 4` for Theorem 2.7), with a nonempty bulk for the block Anderson model;
`docs/PAPER-VS-LEAN.md` §1 lists them.

## Map of the library

Section numbers refer to the paper in `paper/`.

- `RBM3D/Basic.lean`, `RBM3D/Analysis/`: shared notation and the deterministic bound `‖(H − z)⁻¹‖ ≤ (Im z)⁻¹`.
- `RBM3D/Defs/`: the torus `Z_L^d` and its distance, the block variance matrix `S^{(B)}(g)` of (2.5), the semicircle
  law and the flow `z_t`, the parameters `ℓ_t`, `B_{t,K}` and the tail functions, stochastic domination `≺`.
- `RBM3D/Gauss/`: the Gaussian band model on `Z_{WL}^d`, Gaussian integration by parts, the flow calculus.
- `RBM3D/Propagator/`: the propagators `Θ` of §2.4 and their estimates (Appendix A.1).
- `RBM3D/Loop/`, `RBM3D/Hierarchy/`: `G`-loops along the stochastic flow of §2.3, the primitive loops `𝒦` (tree
  representation, Ward's identity and inequality, bounds; Appendix A.5) and the contraction algebra of the loop
  hierarchy.
- `RBM3D/Green/`: Lemma 3.1 (`lem_GbEXP`), the entrywise and averaged local laws from bounds on 2-loops.
- `RBM3D/Kernel/`, `RBM3D/Evolution/`: the evolution kernel and its estimates (§4.4, Appendix A.2–A.4), and the
  central limit step of Step 5 (§5).
- `RBM3D/Path/`: the time grid, martingale bounds and the evolution `𝒰` along the flow (`lem_dec_calE`).
- `RBM3D/Induction/`: the induction of Steps 1–6 (§3–§6).
- `RBM3D/Chain/`: the model-generic form of the induction steps, used for both models.
- `RBM3D/Graph/`: the light-weight term (§7, Appendix B).
- `RBM3D/BA/`: the block Anderson model (§8, Appendix B.3) and Theorem 2.7 for every `d ≥ 3`.
- `RBM3D/Universality/`: bulk universality (Theorem 2.4) and the statement of the external input `UNL32`.
- `RBM3D/Main/`, `RBM3D/Endpoints.lean`: the statements of the main theorems and their assembly (§2.5), with the
  compiled examples.
- `RBM3D/Test/Axioms.lean`: the axiom check.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail: what is proved, every
difference between the Lean statements and the printed ones, uniformity in the sizes, the external input, and where
the Lean proof takes a different route from the paper.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Paper: Sofiia Dubova, Fan Yang, Horng-Tzer Yau and Jun Yin. Lean formalization: Jun Yin.
