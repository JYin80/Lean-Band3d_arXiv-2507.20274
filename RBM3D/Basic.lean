/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

/-!
# RBM3D

A Lean 4 / Mathlib formalization of
*Delocalization of non-mean-field random matrices in dimensions `d ≥ 3`*
(arXiv:2507.20274): the delocalization, local semicircle law, quantum unique ergodicity,
universality and quantum diffusion statements of the random band matrix model (Theorems 2.1-2.5)
and the block Anderson model (Theorem 2.7), for every `d ≥ 3`.  The final statement is
`final_shape` (in Main/FinalShape.lean): all of these hold conditionally on the single external
input `Univ.UNL32` (Theorem 2.2 of Landon-Sosoe-Yau, arXiv:1609.09011v4).

## Layout

The library is in namespace `RBM`; the torus is `RBM.Zd d L := Fin d → ZMod L` with `d` a
parameter.  By directory:

* `Defs/`: the torus `Z_L^d` and its periodic distance, sphere counts and radial lattice sums,
  the parameters `ℓ_t` and `B_{t,K}`, the tail functions `𝒯_t`, the block variance matrix
  `S^(B)(g)`, deterministic and stochastic domination `≺`, the semicircle law and the flow `z_t`,
  and the size data of an admissible sequence.
* `Analysis/`: the resolvent bound `‖(H − z)⁻¹‖ ≤ (Im z)⁻¹`.
* `Propagator/`: the propagator `Θ` and the properties of Lemma 2.19 (`lem_propTH`).
* `Kernel/`, `Evolution/`: the evolution kernel `U^(n)` and its estimates (`lem:sum_Ndecay`,
  `lem:sum_decay`, `lem:sum_decay_nonzero`), `lem:propT`, and the Gaussian replacement step.
* `Loop/`: `K`-loops and `G`-loops, the tree representation, uniqueness, Ward's identity
  (`lem_WI_K`), and `ML:Kbound`.
* `Gauss/`: the Gaussian band model on the fine lattice, Stein's identity, the flow calculus,
  moments and `≺`, and the block Anderson wrapper.
* `Green/`: the resolvent-entry estimates of Lemma 3.1 (`lem_GbEXP`).
* `Hierarchy/`: the contraction algebra of the loop hierarchy.
* `Path/`: the grid walk, Azuma-Hoeffding and stopping times, the kernel `𝒰`, and `lem_dec_calE`.
* `Graph/`: the graphical lemmas (`GtoAG`, `lem:Anp_key_gh`, `lem:LWterm_EXP`) and their block
  Anderson forms.
* `Induction/`, `Chain/`: the induction of Theorem 2.24 (`lem:main_ind`) for the band model, and
  its forms over a carrier.
* `Universality/`: bulk universality (Theorem 2.4, `Thm: B_Univ`), from `UNL32`.
* `BA/`: the block Anderson model (Theorem 2.7, `MR:decol_BA`; `lem:main_ind_BA`).
* `Main/`, `Endpoints`: the assembly of Theorems 2.1-2.5 and 2.7.
* `Test/Axioms.lean`: the axiom audit `#assert_rbm_axioms`, run at the end of the root module:
  every declaration in `RBM` uses only `propext`, `Classical.choice`, `Quot.sound`.

## Two differences from the one- and two-dimensional papers

**`d` is a parameter.**  The one-dimensional paper fixes `d = 1` and the two-dimensional paper
fixes `d = 2` (with the index type `ZMod L × ZMod L`).  Here the lattice is
`RBM.Zd d L := Fin d → ZMod L` and the hypothesis `3 ≤ d` is introduced only where it is actually
used.  In the paper that is exactly two places: the borderline lattice sum
`(eq:latticesum_d3)`, where `d = 3` costs a `log L`, and the `(r+1)^(-(d-2)/2)` decay of `T_t`.

**The propagator decay estimates.**  The `d = 2` paper proves them from scratch in its Section 8.
This paper attributes properties 5-8 of `lem_propTH` to [yang2024Del] Lemma 3.1 and (E.19) and
to [DYYY25] Lemma 2.14, with the details omitted, and Appendix B quotes its three expansion
lemmas from [yang2024Del] B.9-B.11.  They are proved here (`Propagator/Prop5Hold`,
`Propagator/Prop5Short`, `Propagator/Prop6Hold`), so that no project axiom is used: the audit in
`Test/Axioms` admits none.
-/
