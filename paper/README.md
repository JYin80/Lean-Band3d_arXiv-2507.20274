# Paper sources

`2507.20274-inventiones-submission.pdf` — the compiled paper (97 pages), and `tex/` its
LaTeX source, as of the third proofreading round (2026-09-19).

Both are **gitignored**: this directory is a local reference for whoever is doing the
formalization, not part of the published repository.

Section-to-file map (the `\input` order in `tex/main.tex`):

| File | Content |
|---|---|
| `1_2_Intro_model_result.tex` | §1 Introduction, §2 model and main results. §2.5 "Propagators" (`def_Theta`, `defi:ofB`, `lem_propTH`) is the definition layer this project builds on. |
| `3_5_Loop_Hierarchy.tex` | §3–5, Steps 1–5. Stochastic flow and loop hierarchy — **not formalized**. `lem:propT` (§3) is deterministic and is in scope. |
| `6_Step6_two_loop.tex` | §6, Step 6. Stochastic — not formalized. |
| `7_8_light_weight.tex` | §7 light-weight term, §8 block Anderson extension. Mostly stochastic; the graph definitions it uses are in scope. |
| `A_deterministic_estimates.tex` | Appendix A. **The deterministic core.** A.1 proof of `lem_propTH`, A.2 evolution kernel, A.3 `lem:propT`, A.4 `claim:TTk`, A.5 `K`-loop tree representation. |
| `B_graphical_lemmas.tex` | Appendix B. **The combinatorial core.** `def scalingBA`, the three cited expansion lemmas, and the scaling-order bookkeeping proved on top of them. |

The label names in these files are the node names used in `blueprint/src/content.tex`.
