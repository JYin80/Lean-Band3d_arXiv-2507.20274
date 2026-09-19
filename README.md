# Lean-Band3d

A Lean 4 / Mathlib formalization of the deterministic core of
*Delocalization of non-mean-field random matrices in dimensions $d \ge 3$*
(Dubova, F. Yang, H.-T. Yau, J. Yin), [arXiv:2507.20274](https://arxiv.org/abs/2507.20274).

Site: <https://jyin80.github.io/Lean-Band3d_arXiv-2507.20274/>

Sister projects: [`../RBM1D`](https://github.com/JYin80/Lean-RBM1d_arxiv-2501.01718)
($d=1$) and [`../RBM2D`](https://github.com/JYin80/Lean-RBM2d_arxiv-2503.07606) ($d=2$).

## What is here

| Layer | Files | Status |
|---|---|---|
| Lattice $\mathbb Z_L^d$, periodic distance, $B_{t,K}$, $\ell_t$ | `RBM3D/Defs/` | drafted |
| $S^{(B)}$, $M^{(\sigma_1,\sigma_2)}$, $\Theta_t$, $\mathring\Theta_t$ | `RBM3D/Defs/Block.lean`, `RBM3D/Propagator/Basic.lean` | drafted |
| Propagator properties 1–4 (the paper proves these) | `RBM3D/Propagator/Props14.lean` | drafted |
| Propagator properties 5–8 (the paper cites these) | `RBM3D/Propagator/Interface.lean` | axioms |
| Graph expansion lemmas (the paper cites these) | `RBM3D/Graph/Expansions.lean` | axioms |
| Scaling-order bookkeeping (the paper proves this) | `RBM3D/Graph/ScalingOrder.lean` | drafted |

`docs/PLAN.md` has the roadmap, `docs/TASKS.md` the work queue, `docs/STATUS.md` the
current state, `docs/paper-deltas.md` every place a Lean statement departs from the
paper's literal one.

## Building

```bash
cd ~/Lean_proof/RBM3D
lake exe cache get
lake build
```

Lean `4.34.0` / Mathlib `v4.34.0`, the same as both sister projects.

## Dimension

`d` is a parameter throughout: the lattice is `RBM.Zd d L := Fin d → ZMod L`, and the
hypothesis `3 ≤ d` is introduced only where the mathematics actually needs it. In the
paper that is exactly two places — the borderline lattice sum where $d=3$ costs a
$\log L$, and the $(r+1)^{-(d-2)/2}$ decay of $\mathcal T_t$.
