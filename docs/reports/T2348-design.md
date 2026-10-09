# T2348 (LW-13b-D) design: provenance, domains, G2, `ℓ^∞`, assembly for `lwMomentExp_holds` (`lem:LW_moment_exp`)

Prover `claude-sonnet-5-5` (prover-max, stage 1b = the design). Branch `t/T2348` (base `692a72b`), probe `RBM3D/Probe/T2348Pins.lean` (598 lines, limit 600), commit `9f3bd75`; the probe stays on the branch, never merged. Last edit: Fri Oct  9 00:40:33 UTC 2026 (`date -u` at the final edit).
Citations: `path.lean:line` is at the base of the branch, path relative to `RBM3D/`; paper `7_8:line` is `paper/tex/7_8_light_weight.tex`, `1_2:line` is `1_2_Intro_model_result.tex`; "probe NNN" is line NNN of the probe; "(a) row k" is row k of the exponent table in `docs/reports/T2348-prove.md`; `T2348.md:N` is line N of the ticket `docs/tickets/T2348.md`, `2244.md:N` is line N of `docs/supervisor/2026-10-08-2244.md`.
Evidence: Lean side (build, axioms, statements, instances, name-clash) in `docs/reports/T2348-prove.md` (b); sizes, rows, the de-privatisation list, the long statements and the echo of every citation of this report in section 10 below.

## 0. The answer

| item | answer (one line) | evidence |
|---|---|---|
| 1 provenance | Every `LocStepX` step has vertex maps `π` (inclusion `owxEmb k`, then the quotient `vmap` of the dotted-edge partition), independent of `m` and of the input tag, that are label-compatible (`ExtOK`), molecular, and make the weighted expectation identity `WExp` hold. **No constructor is non-pointwise**: each identity is proved at one labelling `(ℓe, ℓi)` of all vertices of the input and the sum over `ℓi` is taken afterwards; the merges are label-compatible reindexings. No real twin: the weighted twins of the wrappers are 905 source lines, row P central 1440 (1003-2170). | section 2; probe 77-170 |
| 2 domains | The weight sits on the initial `β^{(k)}`; every internal molecule of every output contains some `π β^{(k)}` (compiled `Molecular.comp`, `CoverBy.comp`). **Route (R)**: root each internal molecule at that vertex (the paper's free centre, `7_8:860`); then the aux domain is exactly the weight domain: far = the merged `AnpFarAndAt`, near = `AnpNearInfAt`, **no `Rb` enlargement, no `λ`**. Needs `GtoAG` for a weighted sum rooted at chosen representatives, `LWGtoAGRooted` (it implies `LWGtoAG`, compiled), a new row G (≈ 470 lines): the supervisor's reading that the pins "can stay as merged in shape" with the domain enlarged (2244 R1) does not reach `GtoAG`: `lwGtoAG_holds` bounds the sum over all internal labels, so the weighted sum needs the restricted (rooted) twin. **Route (E)** (enlarge by `Rb`): `farDAnd` takes the radius but `AnpFarAndAt` has one `ℓ` for domain and cap, so the enlarged pin is the merged one at `max(ℓ-Rb, 0)` plus a cap conversion of cost `(Rb+1)^{(d-2)/2} e^{½√(Rb/ℓ_t)}`, not `e^{½√(Rb/ℓ_t)}` (compiled, sharp); `nearD`/`tau` share one `ℓ`: not a restatement. | section 3; probe 189-227, 407 |
| 3 G4 | `f = f^> + f^(a) + f^(b)` is an exact identity (compiled `LWf_split`); `domFar` is the merged `farDAnd` (`domFar_eq`), `domNearA ⊆ ball_∞(a, ℓ)`, `domNearB ⊆ ball_∞(b, ℓ)`, single centres. | section 4; probe 248-320 |
| 4 G2 | `LWXiExpClaim`: twin of `lwXiClaim_holds` with the comparability `Φ(m) ≤ Kn Φ(ℓ)`, `ℓ ≤ m + 2ρ`, given by the compiled shift lemma, class `Φ_E = C₀ sfT(·∧ℓ) + W^{-D'}`; radius condition `√ρ ≤ τ log N` eventually: `ρ = 2K(log W)^{3/2}+1` passes, Lean's `K(log W)²` never; `(log W)^{3/2}` tail copy compiled (`lwTail32`, threshold `log W ≥ (2A/(𝔠c))²`). | section 5; probe 396-470 |
| 5 Met | `EKTTkInf`, `AnpNearInfAt` stated; the new analytic content (the `ℓ^∞` lattice sum, constant `d^{k+2} ballC_k`) is compiled; the generic chain has no `zdist` in `Graph/LWMomExp.lean:304-516`, but the twin of `near_graph` needs **10** `private` keywords removed, not the 2 of the ticket (script, section 10). | section 6; probe 335-394 |
| 6 (A), Asm | `LWMomExpNoExp`, `LWMomExpFarPin`, `LWMomExpNearPin`, `LWMomentExpOfParts` over `LWMomentExpOn` with the regime `regA K` compile; the pointwise assembly step `norm_add3_pow_le` is compiled. | section 7; probe 507-538 |
| 7 rows | Three rows: R1 = P (provenance engine) 1003/1440/2170; R2 = M + X (`ℓ^∞` near chain, G2, tail, (A)) 1182/1573/2344; R3 = G + F (rooted `GtoAG`, expansion argument, assembly, registry) 1183/1567/2337 lines (lo / central / hi). LW: 47 now, 48 with T2348, 49-51 the rows, **LW-01 = 52**; the pre-named cuts add up to three rows. | section 8 |

**Verdict: PASS** for route (a): no mathematical item is open, every piece has a compiled statement and a route. Findings that change earlier readings: (i) the cost of the cap shift has the factor `(ρ+1)^{(d-2)/2}` (the ticket `T2348.md:7`, supervisor 2244 R1 `2244.md:28` and `T2344-prove.md:23` state it without); (ii) the weighted sum has to be carried through `GtoAG` (new row G); (iii) the `Rb`-enlargement of the domain is avoidable by rooting; (iv) the de-privatisation list has 10 entries; (v) `LocStepX.eval` is a list identity without labels, the analytic identity is `lvl1_step_identity` (section 2).

## 1. What the merged code contains (the inputs of the design)

* The engine: `LocStepX` (`Graph/LWEngine.lean:391`, constructors `weight` `:392`, `edge` `:395`, `gg` `:400`) over the carrier `(ℕ × ℕ) × PGraph (Fin 2)` (`lwEvX`, `Graph/LWEngine.lean:57`); `LocStepX.eval` (`Graph/LWEngine.lean:418`) is the **list-level** naturality `LocStep m (lwEvX m (t0, P)) (…)`, it contains no label. The recursion `lwEngine_combine` (`Graph/LWEngine.lean:628`), `lwEngine_exists` (`Graph/LWEngine.lean:667`), `lw_localregularX` (`Graph/LWEngine.lean:771`); its analytic identity is conjunct 4 of `LWLocRegConcl` (`Graph/LWEngine.lean:68-75`), proved from `lvl1_step_identity` (`Graph/LWLvl1.lean:3590`).
* `GtoAG`: `LWGtoAG` (`Graph/AuxGraph.lean:979`), `lwGtoAG_holds` (`Graph/AuxGraph.lean:1018`) bounds `‖Γ.val‖` by the sum over **all** internal labels, through `auxGraph_main_sum` (`Graph/AuxGraph.lean:901`) with the roots chosen by `auxGraph_exists_forest` (`Graph/AuxGraph.lean:459`, `choose` at `:476`); `auxVal` sums all block labels (`Graph/AuxGraph.lean:79`).
* The pins: far `AnpFarAndAt` (`Graph/LWMomExpFar.lean:80`, domain `lwMomExpFar_farDAnd`, `:42`), proved `lwMomExpFar_and` (`Graph/LWMomExpFar.lean:338`); near `AnpDetNearAt` (`Graph/LWMomExp.lean:900`, `ℓ¹`, domain `lwMomExp_nearD`, `:532`), proved `lwMomExp_near` (`Graph/LWMomExp.lean:1023`); the target `LWMomentExp` (`Graph/LWPins.lean:341`), registry line `Test/Axioms.lean:160`.
* G2: `lwXiClaim_holds` (`Graph/AuxGraph2.lean:965`) uses `LWPsiAll` through `auxGraph2_phi_cmp` (`Graph/AuxGraph2.lean:723`); radius `Rb = K (log W)²` at `Graph/LWMoment.lean:1048`, tail `Graph/LWMoment.lean:473`.

## 2. Item 1: the provenance lemma over `LocStepX`

**Statement** (compiled). `WExp m P outs` (probe 77) says: for every real weight `W` on the labellings of the vertices of `P`, `E[pvalW P W ℓe] = Σ_{o ∈ outs} E[pvalW o.Q (W ∘ π_o) ℓe]` at the data of conjunct 4 (`LWExpData`, probe 69), with `valW Γ D W ℓe = Σ_{ℓi} W(ℓe, ℓi) · Γ.term D (ℓe, ℓi)` (probe 34; `W ≡ 1` is `LGraph.val`, `pvalW_one`). `LocStepXProv` (probe 157): for every `LocStepX P LX` there are maps `π r : P.E' ⊕ P.I' → r.2.E' ⊕ r.2.I'`, chosen before `m` and `t0`, such that for every `m`, `t0` the evaluated outputs are `ExtOK` (the external vertices go to the external vertices), `Molecular` (probe 64: a molecule goes into a molecule; every internal molecule of the output is the image of an internal molecule of the input) and `WExp m (lwEvX m (t0, P))` holds. `LWEngineProv` (probe 164) is `lw_localregularX` with the maps, `ExtOK`, and the coverage `Cover` (every internal molecule of every output contains some `π β^{(k)}`); `lwEngineProv_imp_localregularX` (probe 173, proved) shows it strengthens the merged engine. The weighted identity of the ticket is `WExp.prod` (probe 111, proved): `W = Π_k w_k(ℓ β^{(k)})` gives `E[Π_k f^{w_k}] = Σ_r E[Σ_{ℓ_i} Π_k w_k(ℓ(π_r β^{(k)})) term_r]`, with `E[Π_k f^{w_k}] = E‖LWfD‖^p` when `w_k = 1_D ∘ blk` (the bridge P6, section 8, twin of `lwMoment_fxyPow_val`, `Graph/LWMoment.lean:1748`).

**Constructor-by-constructor table** ("decided at" = the proof step that fixes the answer):

| step | `π` | pointwise in the old labels? | decided at |
|---|---|---|---|
| `weight` (`Graph/LWEngine.lean:392`): outputs `lwSymmOwxT1..4` = `owxExt (owxEmb k)` | **inclusion** `owxEmb k = Sum.map id Sum.inl` (`Graph/LWWeightExp.lean:454`), then the quotient of the partition | **yes** | `owx_term_integral` (`Graph/LWWeightExp.lean:1060`) is stated at one labelling `(ℓe, ℓi)`, the extended labelling restricts to it (`owxLab1_emb`, `Graph/LWWeightExp.lean:1046`); `owx_graph_E` takes the sum over `ℓi` afterwards (`hL`, `Graph/LWWeightExp.lean:1333`; `simp_rw` `:1339`), and so does `owxE_graph_E` for `x` external or internal (`hL` `Graph/LWSymm.lean:1174`; `simp_rw` `:1180`) |
| `edge` (`Graph/LWEngine.lean:395`): `owxT1` (leaf), `oe1xD`, `oe1xP3..P6` = `owxExt (owxEmb 1)` | inclusion (`Graph/LWEdgeExp.lean:606`, `:1084-1116`); the merge `oe1xT1` (`relabel oe1xPhi`, quotient, `Graph/LWEdgeExp.lean:863`) is **not an output** (`lvl1EdgeOuts0`, `Graph/LWLvl1.lean:3236`) and has termwise value `0` on a normal graph (`lvl1_val_zero_of_xself`, `Graph/LWLvl1.lean:3373`, used `Graph/LWLvl1.lean:3389`) | **yes** | `oe1x_term_integral` (`Graph/LWEdgeExp.lean:654`), `oe1x_graph_Ed` (`Graph/LWEdgeExp.lean:827-828`); the loop split `oe1xDs_integral` is termwise (`hsplit`, `Graph/LWEdgeExp.lean:1269-1279`; `oe1xD_red_term` `:1123`) |
| `gg` (`Graph/LWEngine.lean:400`): `R2` = `owxExt id`, `R3..R8` = `owxExt (owxEmb k)` | inclusion (`Graph/LWGGExp.lean:485`); the merge `R1` (`oe2xPhi`, `Graph/LWGGExp.lean:560`) is not an output (`lvl1GGOuts0`, `Graph/LWLvl1.lean:3243`), termwise `0` (`Graph/LWLvl1.lean:3408`) | **yes** | `oe2x_term_integral` (`Graph/LWGGExp.lean:1243`), `oe2x_graph_E` (`Graph/LWGGExp.lean:1574-1614`) |
| dotted-edge partition inside the three (`lvl1*Outs0`, `Graph/LWLvl1.lean:3228-3249`) | **quotient** `LGraph.vmap` (`Graph/LWVocab.lean:768`); `extMap` on the external vertices | **yes**, a label-compatible reindexing | `term_eq_sum_dotChoices` (`Graph/LWVocab.lean:1168`) and `val_splitWeights` (`hterm`, `Graph/LWVocab.lean:1253-1260`) are pointwise in `ℓ`; `val_eq_merge_val` (`Graph/LWVocab.lean:881`): `term_merge` (`:850`), `hlab` (`:885`: old labels = new labels `∘ vmap`), the bijection `Φ` (`:884`), `hrange` (`:906`, labels breaking a `=` edge have term `0`); `mergeP_val` (`Graph/LWVocab.lean:938`) |
| twist `(c, t)` in `lwSymm_*_graph_E` (`Graph/LWSymm.lean:1590`, `:1639`, `:1690`) | identity on the vertices | **yes**, real weights commute with `lwSymmCj` | `lwSymm_term_conj` (`Graph/LWSymm.lean:232`), `lwSymm_term_transpose` (`Graph/LWSymm.lean:246`), `lwSymmUncirc_term` (`Graph/LWSymm.lean:1418`) are pointwise in `ℓ`; the flip acts on `ω` only (`lwSymm_integral_flip`, `Graph/LWSymm.lean:465`; `lwSymm_twist_integral`, `:558`) |
| pack `lvl1Pack` (`Graph/LWLvl1.lean:3252`) | internal vertices fixed, `ext` composes | **yes** | `lvl1_pack_identity` (`Graph/LWLvl1.lean:3450`), `PGraph.lvl1Comp_val` (`Graph/LWLvl1.lean:3105`): external labels only |
| tags `(j, j')` (`lwEvX`, `Graph/LWEngine.lean:57`) | none (scalar `m^j m̄^{j'}`) | yes | `lwEngine_blk_nat` (`Graph/LWEngine.lean:178`) |

**Answer to "if some constructor is not pointwise"**: none. The old internal labels are never summed before the step identity is applied, and no step renames them. So the generic lemma needs no real twin (1500-2500); the cost is the weighted twin of the *wrappers*: the term-level lemmas are reused as they are. Molecular: every output keeps the waved edges of the input mapped by the embedding (`owxExt`, `Graph/LWWeightExp.lean:458`; the count `nWS` never falls, `lwEngine_locStep_nWS`, `Graph/LWEngine.lean:560`), every new vertex is joined to the expansion vertex by an appended waved edge (`owxExt_reach1`, `Graph/LWWeightExp.lean:705`, one new vertex; `owxExt_nM`, `:591`; the paper says "a path of dotted or waved edges", `7_8:351`), `merge` identifies vertices of one `=`-class, which are adjacent in `LGraph.adj` (`Graph/LWVocab.lean:157`); the counting shadow is `Q.g.nM ≤ nM` (`Graph/LWEngine.lean:66`).

**Derivation of the weighted identity from the step lemma** (a sketch in four lines, the compiled parts are marked): (1) `WExp.refl` (leaf, probe 96) and `WExp.comp` (probe 101: if `P` expands to `outs` and every output to `outs' o`, then `P` expands to the composites with the maps composing) are the recursion step of `lwEngine_combine`; (2) `lwEngine_exists` is rerun with `ProvOutX` lists (tags as in `lwEngine_flat_eval`, `Graph/LWEngine.lean:654`) and the two invariants `ExtOK` (composes), `Molecular` (`Molecular.comp`, probe 88); (3) `Cover` for the start graph `fxyPowGraph p` is the initial coverage (each initial molecule is `{α_k, β_k}`, `Graph/LocalRegular.lean:1354`) propagated by `CoverBy.comp` (probe 125); (4) `WExp` with `W ≡ 1` is conjunct 4 (`pvalW_one`), which is why `lwEngineProv_imp_localregularX` holds. Evidence: probe compiles with standard axioms only (prove report B2).

## 3. Item 2: the molecule-level domain pins

**Why the weight reaches every auxiliary vertex.** By `Cover`, every internal molecule `c` of an output contains a vertex `π β^{(k)}`; that vertex is internal (`c` has no external vertex), so `rep c := π β^{(k(c))} : I` is a representative with `molOf (inr (rep c)) = c`. A weight `Π_k 1_D(blk ℓ(π β^{(k)}))` is nonzero only if the block of every `rep c` is in `D`.

**Route (R), recommended: root the molecule at its weighted vertex.** The paper lets the centre of a molecule be any vertex of it (`7_8:860`), and the T2289 analysis already used `α_i := β^{(k)}` (`T2289-prove.md:96`, delta `T2289d`). In Lean the centre is the root chosen by `choose` in `auxGraph_exists_forest` (`Graph/AuxGraph.lean:476`), nothing else in the proof of `lwGtoAG_holds` depends on that choice (`hpt`, `Graph/AuxGraph.lean:1078`; the sums `Graph/AuxGraph.lean:1115-1127`). So: (R1) `auxGraph_exists_forest` with the roots as a hypothesis `rep` (a copy without the `choose`, `Graph/AuxGraph.lean:459-537`); (R2) `auxGraph_main_sum` (`Graph/AuxGraph.lean:901`) with the indicator of `∀ c, blk(x c) ∈ Dm` inside `Φ` (the proof sums over `Φ(ℓi ∘ root)`, `Graph/AuxGraph.lean:936-968`, so `Φ·1` is again nonnegative and the same argument applies; `auxGraph_sum_blocks`, `Graph/AuxGraph.lean:663`, is generic in `g`); (R3) `lwGtoAG_holds` with `‖Σ_{ℓi} W term‖ ≤ Σ_{ℓi, W ≠ 0} ‖term‖` and the tail unchanged (`auxGraph_tail_sum`, `Graph/AuxGraph.lean:798`, sums over all labels and the restricted sum is smaller). Compiled statement `LWGtoAGRooted` (probe 197): the hypotheses of `LWGtoAG` verbatim, plus `rep`, a weight `Wt` with `|Wt| ≤ 1` supported where every root's block is in `Dm`, and the restricted `auxValOn` (probe 189); `gtoAGRooted_imp` (probe 227, proved) shows `LWGtoAGRooted d → LWGtoAG d` (`Dm = univ`, `Wt ≡ 1`), so the rooted statement is consistent with the merged theorem. The bridge to the nested form is `LWAuxNestedOwnOn` (probe 218): the restricted twin of `auxGraph_val_eq` (`Graph/AuxGraph.lean:1526`) and of `LWAuxNestedOwn` (`Graph/LWMomExpFar.lean:96`).

With (R) the pins need **no radius at all**: the aux internal vertices lie exactly in the weight domain, so

* far: the merged `AnpFarAndAt` (`Graph/LWMomExpFar.lean:80`) with `S = piFinset (farDAnd a b ℓ)`; `HeadFar` (`:57`, the claim `T2289d`) holds because the first step of path `i` ends at an internal vertex whose block is in the domain; probe 565 (`AnpFarAndAt 3 figAux`, instance) and `domFar_eq` (probe 262) show `farDAnd` for constant paths is `domFar`;
* near: `AnpNearInfAt` (probe 346): `AnpDetNearAt` with `zdistInf`, domain any set in an `ℓ^∞` ball of radius `ℓ` around a centre `c`, same `ℓ` as the cap; the split of section 4 puts `c = a` or `c = b`.

**Route (E) (supervisor 2244 R1, `2244.md:28`): enlarge the domain by `Rb`.** Confirmation of the question asked: (i) `lwMomExpFar_farDAnd d L a b ℓ` takes the radius as an argument (`Graph/LWMomExpFar.lean:42`), so the enlarged domain is `farDAnd a b (ℓ - Rb)`; but `AnpFarAndAt` uses one `ℓ` for the domain and for the cap `ξ ≤ 𝖳(|·| ∧ ℓ)` (`:80-89`); `𝖳` is antitone, so `ξ ≤ 𝖳(·∧ℓ) ≤ 𝖳(·∧ℓ')` for `ℓ' ≤ ℓ` and the merged pin applies at `ℓ' = max(ℓ - Rb, 0)`; the conclusion `Π_i 𝖳(|a_i - b_i| ∧ ℓ')` is converted back by `𝖳(min(r, ℓ')) ≤ 𝖳(max(min(r, ℓ) - Rb, 0)) ≤ Kn 𝖳(min(r, ℓ))` with the compiled `sfT_shift_le` (probe 407): `Kn = (Rb+1)^{(d-2)/2} e^{½√(Rb/ℓ_t)}`, **not** `e^{½√(Rb/ℓ_t)}`; the enlarged far pin therefore reads `Γ.valOn ξ a b (piFinset (farDAnd a b (max (ℓ - Rb) 0))) ≤ C θ^q 𝖳(0)^{ord - p} Π_i Kn 𝖳(min(|a_i - b_i|, ℓ))` for `ξ ≤ 𝖳(·∧ℓ)`; the bound is attained at `s = ρ` ((a) row 2: log ratio `21.0074` against `17.4542`, difference `(d-2)/2 · log(Rb+1) = 3.5531`), so the factor is necessary (delta `T2348a`). (ii) `lwMomExp_nearD` (`Graph/LWMomExp.lean:532`) has the radius as an argument, but `lwMomExp_tau` (`:521`), `lwMomExp_TTkBody` (`:584-593`) and `AnpDetNearAt` (`:900`) use the same `ℓ` as domain radius and cap, and a domain radius `ℓ + Rb` with cap `ℓ` is not covered (the hypothesis `ξ ≤ 𝖳(·∧ℓ)` does not give `ξ ≤ 𝖳(·∧(ℓ+Rb))`, the wrong direction): **not a one-line restatement**. Two fixes: the two-scale split at the inner radius `ℓ₁ = ℓ - Rb` (near domains `ball(·, ℓ₁)`, enlarged to `ball(·, ℓ)`, far domain `farDAnd(ℓ - 2Rb)`; no new pin), or a `λ`-twin with domain radius `λℓ`, constant `(dλ)^{k+2} ballC_k` ((a) row 8). Route (E) needs the unrooted restricted `GtoAG` (`blk(β) ∈ D` and `|blk β - blk(root)| ≤ R` give `blk(root) ∈ D^{+R}`) and the clamp for `ℓ < 2Rb`; its cost is the same row G plus the conversion lemma and two cost factors in the exponent table. It is the fallback if the rooted forest meets a snag.

**Where `Rb` still enters (both routes)**: the radius `R ≥ |E ⊕ I| r` of the premise `hξ` of `GtoAG` (`Graph/AuxGraph.lean:991-993`), hence the radius `ρ = 2R + 1` of G2 (section 5), and the tail `e^{-c r/2}` at `r = (log W)^{3/2}`. In route (R) it enters nowhere in the pins.

## 4. Item 3 (G4): the three-way split

Statements (probe 248-320, all compiled): `domFar a b ℓ = {c : |a-c|_∞ > ℓ ∧ |b-c|_∞ > ℓ}`, `domNearA a ℓ = {c : |a-c|_∞ ≤ ℓ}`, `domNearB a b ℓ = {c : |a-c|_∞ > ℓ ∧ |b-c|_∞ ≤ ℓ}`; `dom_union` (they partition `Z_L^d`), `dom_disj`; `LWfD` (probe 292) is `LWf` (`Graph/LWPins.lean:199`) with the sum over `β` restricted to the blocks in `D`; `LWfD_union` (disjoint `D₁ D₂`) and **`LWf_split`** (probe 313): `LWf x y = LWfD domFar + LWfD domNearA + LWfD domNearB` with `a = [x]`, `b = [y]`, an identity for every sample. `domNearA` lies in the `ℓ^∞` ball of radius `ℓ` around `a`, `domNearB` in the one around `b` (single centres, no `2^q` and no intersection domain). The pointwise step of the assembly is `norm_add3_pow_le` (probe 322): `‖a+b+c‖^p ≤ 3^{p-1}(‖a‖^p+‖b‖^p+‖c‖^p)`, so `E|f|^p ≤ 3^{p-1} Σ E|f^•|^p`, and each part carries the same right-hand side as the target. Paper: the decomposition is `7_8:1607-1611` with `|a_1-a| ∨ |a_1-b|` in both parts, the far lemma assumes `D_{>ℓ}` at `7_8:1633`, the near lemma `D_{≤ℓ}` at `7_8:1648` (the intersection of the two balls); the merged `farDAnd` is the "and" domain (`Graph/LWMomExpFar.lean:16-18`, definition `:42`, DECISIONS §95), and with it the paper's path claim "every path contains at least one long ending edge" (`7_8:1637-1638`) holds at the first step, which `HeadFar` states. Under (R) the thresholds are the plain `ℓ`.

## 5. Item 4 (G2): the exp-class `ξ` bound at radius `(log W)^{3/2}`

**Statement** (probe 446-463): `LWXiE` is `LWXi` (`Graph/LWPins.lean:360`) with the class function `𝖳_t(|·|_∞ ∧ ℓ) + W^{-D}` and the Ward bound; `LWXiExpClaim d` is `LWXiClaim` (`Graph/AuxGraph2.lean:951`) with the hypotheses `LWPsiAll`, `LWLoop2` replaced by `LWAssmExp` (`Graph/LWPins.lean:283`), the radius hypothesis `∀ τ > 0, ∀ᶠ n, √(ρ n) ≤ τ log N_n`, and the conclusion `LWXiE … (lwXiVar … ρ)`.

**Route.** Copy `lwXiClaim_holds` (`Graph/AuxGraph2.lean:965-1098`, 133 lines) with the one hypothesis `hcmp : Φ m ≤ Kn Φ ℓ` for `ℓ ≤ 2ρ + m` (used at `Graph/AuxGraph2.lean:1019`) taken as an input instead of being derived from `LWPsiRel` by `auxGraph2_phi_cmp` (`Graph/AuxGraph2.lean:723`). For the class `Φ_E(r) = C₀ 𝖳_t(r ∧ ℓ) + W^{-D'}`: `LWLoopExp` gives `LWLoop2` for `Φ_E` (the zero-mode term of `tailT` is dominated for `s ≤ L` by `zeroMode_le_of_ge`, `Defs/Tail.lean:119`, (a) row 5), and `hcmp` is the compiled **`sfT_shift_le`** (probe 407, with `ρ ↦ 2ρ`; proof `sqrt_le_add_sqrt_shift`, probe 396, and `(s+1) ≤ (ρ+1)(max(s-ρ,0)+1)`): `Kn = (2ρ+1)^{(d-2)/2} e^{½√(2ρ/ℓ_t)}`; the additive `W^{-D'}` is absorbed since `Kn ≥ 1`. The condition `Kn ≤ N^{τ/8}` (`Graph/AuxGraph2.lean:1019-1021`) holds iff `√ρ = o(log N)`: `ρ = 2K(log W)^{3/2}+1` passes, `ρ = 2K(log W)²+1` (Lean's `Rb = K(log W)²`, `Graph/LWMoment.lean:1048`) never ((a) rows 5-6: ratio `K√K/3.6 = 4.08 > τ` at `K = 6`; first crossing at `log W = 4.45·10⁷` for `(log W)^{3/2}`). Hence the radius is the truncation radius of the *waved-edge tail*, not of `LWGbyXi` (`R` is free subject to `2R + 1 ≤ ρ`, `Graph/AuxGraph2.lean:1114`): the tail copy `lwTail32` (probe 467, proved) is `lwMoment_tail` (`Graph/LWMoment.lean:473`) with `(log W)^{3/2}`, threshold `log W ≥ (2A/(𝔠c))²` instead of `≥ 2A/(𝔠c)`, instance at `sz0` (probe 591). Floor: the `W^{-D}` edges of `ξ ≤ 𝖳 + W^{-D}` expand `Π(𝖳 + W^{-D})`; every term with a floor edge is `≤ 2^{|E|} N^q W^{-D}` and is absorbed by `D' = D + (q+1)/𝔠` (the `+ W^{-D}` of the target). No finite witness of the conclusion is claimed: closure is `∀τ ∀ᶠ n`, as for every merged `≺`.

## 6. Item 5 (Met): `claim:TTk` and the near pin in `ℓ^∞`

Compiled: `EKTTkInf` (probe 335: `EKTTk` of `Evolution/Pins.lean:156` with `zdistInf` and the domain in an `ℓ^∞` ball around a centre `c`), `AnpNearInfAt` (probe 346), and the new analytic content `sum_ball_inf_min_pow_le` (probe 358): for `D` in the `ℓ^∞` ball of radius `ℓ` around `c`, `Σ_{α∈D} (min(|x-α|_∞, ℓ)+1)^{-k} ≤ d^{k+2} ballC_k ℓ²`, from the merged `ℓ¹` lemma `sum_ball_min_pow_le` (`Defs/RadialSum.lean:367`) at radius `dℓ` through `zdistD ≤ d zdistInf` (`Defs/Sizes.lean:122`); instance at `d = 3`, `L = ℓ = 5` (probe 581).

Route (the supervisor's "delete `private` from `Graph/LWMomExp.lean:310` and `Graph/LWMomExp.lean:434` and restate in `ℓ^∞`", amended): the path-system chain `lwMomExp_step_aux`, `lwMomExp_sys_bound` is generic in `w`, `D` (no `zdist` occurs in `Graph/LWMomExp.lean:304-516`, script B6). The twin file copies the norm-specific segments (tau block `Graph/LWMomExp.lean:521-581`, `TTkBody` to `sys_near` `:584-699`, `near_graph` with its two private helpers and `lwMomExp_near`, `:918-1024`) and the kernel lemmas `sfT_pair_le` (`Kernel/PropT.lean:788`), `prod_sfT_pair_le` (`:839`), `key_T_reduce` (`:913`), `key_T_reduce_absorbed` (`:1056`) with `zdistD ↦ zdistInf` (triangle: `anpKey_zdistInf_tri`, `Graph/AnpKey.lean:101`), and `ekTTkInf_holds` from `key_T_reduce_absorbed` and the ball sum. **The keyword list is 10, not 2**: the twin of `near_graph` also uses `lwMomExp_chain_nonneg` (`Graph/LWMomExp.lean:152`), `lwMomExp_walk_chain` (`:752`), `lwMomExp_path_ne` (`:835`), `lwMomExp_sysOf_length` (`:846`), `lwMomExp_sysOf_mem` (`:851`), `lwMomExp_pathEdges` (`:862`), `lwMomExp_pathEdges_card` (`:874`), `lwMomExp_prod_split` (`:882`) (script B6; their own dependencies stay private inside the file). The `ℓ¹` pins stay as merged; the rescale `ℓ_t ↦ dℓ_t` is not used ((a) T2344 row 9).

## 7. Item 6: (A) and the assembly against the new pins

`LWMomentExpOn d dom reg` (probe 507) is `LWMomentExp` (`Graph/LWPins.lean:341`) for `f^{dom}` on the pairs/lengths in `reg` (`dom ≡ univ`, `reg ≡ True` is the target). The regime `regA d K` (probe 521): `|a-b|_∞ ≤ K (log W)^{3/2} ℓ_t ∨ ℓ ≤ K (log W)^{3/2} ℓ_t` (the paper's `7_8:1602` with a free `K`; delta `T2348b`). **(A)** `LWMomExpNoExp d K` (probe 527): `lwMoment_holds` (`Graph/LWMoment.lean:1785`) with the B class `LWPhiB`, `K_n = min ⌊ℓ⌋ L`, `c₀ = d`, as T2342 (`lwtermExpN_of_LWterm`, `Graph/LWTermExpN.lean:414`, 546 lines for the same shape); the loss `e^{(p/2)√K (log W)^{3/4}}` is `≤ N^τ` once `log W ≥ (p√K/(2·3.6τ))⁴` (`3.4·10⁴` at `p = 2`, `K = 6`, `τ = 0.05`, (a) row 6 has the same formula). **Far/near pins** `LWMomExpFarPin d K`, `LWMomExpNearPin d K` (probe 529-534): `LWMomentExpOn` for `domFar`, `domNearA`, `domNearB` on `¬ regA K`, with the same right-hand side as the target. **Assembly** `LWMomentExpOfParts` (probe 537): `∀ K, (A) → far → near → LWMomentExp d`; proof = `LWf_split` and `norm_add3_pow_le` pointwise, `E|f|^p ≤ 3^{p-1}Σ E|f^•|^p` (integrable, bounded), and the union of two `Prec` statements over `regA ∨ ¬regA` (the `by_cases` of `lwMoment_holds`, `Graph/LWMoment.lean:1810-1812`). `K` is the card bound of the engine lists (`Graph/LWMoment.lean:1034-1038`); in `¬ regA K` the pair is at block distance `> K (log W)^{3/2} ℓ_t ≥ K r`, the condition of `lwScalemole`, so the outputs with `𝓜_x = 𝓜_y` are tail-negligible (`lwMoment_prec_scale`, `Graph/LWMoment.lean:925`, with `(log W)^{3/2}`). The exponent bookkeeping is (a) rows 1-12 (`n_M ≤ p`, `2p ≤ ord`, `Λ^{2q} ≤ N^τ`, `η_t ≍ 1-t`); unchanged under (R).

## 8. Item 7: the proving rows

Sizes are estimates: the measured code lines of the merged declarations that a piece twins (script B5, section 10) times (lo / central / hi) multipliers, plus new code in absolute lines; every base, multiplier and absolute number is printed in B5. All rows: role `prover-max` (Sonnet, effort max), stage 1a is the row's own design check, stop line (binding, DECISIONS §148 (5)) 0.9 × hi.

| row | content | sole writable files | lo / central / hi (stop) | depends on | registry |
|---|---|---|---|---|---|
| **R1 = P** (provenance engine) | `LocStepXProv`: weighted partition (`val_eq_partition` twin), the three step identities, twist, pack, maps with `ExtOK`/`Molecular`; recursion with maps and `Cover`; the weighted bridge `pvalW (fxyPowGraph p).pack (lwMoment_D …) (fun ℓ => Π_k 1_D(blk ℓ(β_k))) ![x, y] = ‖LWfD … D x y‖^p`; `lw_localregularXP : LWEngineProv` | `Graph/LWProv.lean` | 1003 / 1440 / 2170 (1950) | merged only | none |
| **R2 = M + X** | `EKTTkInf`, `AnpNearInf`; G2 `LWXiExpClaim`; `lwTail32`; (A) `LWMomExpNoExp` | `Graph/LWMomExpInf.lean`, `Graph/LWXiExp.lean`, `Graph/LWMomentExpA.lean`, `Graph/LWMomExp.lean` (the 10 keywords only; audited by script as supervisor 1942 O3) | 1182 / 1573 / 2344 (2100) | merged only | none |
| **R3 = G + F** | `LWGtoAGRooted`, rooted forest, `LWAuxNestedOwnOn`; the expansion argument for the three domains, the two pins, `lwMomentExp_of_parts`, `lwMomentExp_holds : ∀ d, LWMomentExp d` | `Graph/AuxGraphRooted.lean`, `Graph/LWMomentExp.lean`, `Test/Axioms.lean` | 1183 / 1567 / 2337 (2100) | R1, R2 merged | delete the owed line `LWMomentExp` (`Test/Axioms.lean:160`) |

R1 and R2 run in parallel (no shared file); R3 after both. **Pre-named cuts** (taken by the row's stage 1a if its central estimate exceeds 1800, without a new dispatcher decision, as in T2344): C1 R1 → P-a (`LocStepXProv`, ≈ 1000 central) | P-b (recursion, `Cover`, bridge, ≈ 450); C2 R2 → M (646) | X (927); C3 R3 → G (473) | F (1094); a cut moves the second part to a new row and the pin of the first part enters `owedProps` until then (comment "LW-13b").

**LW count.** 47 now (supervisor 2244, `2244.md:55`; the ticket `T2348.md:12`); T2348 = 48; R1, R2, R3 = 49, 50, 51; **LW-01 = 52**; each cut adds one row (up to 55). Conditions of supervisor 2244 R3 (`2244.md:42`): (i) the provenance lemma is pointwise and is one row: yes (central 1440, the top of the supervisor's 800-1500, hi 2170); (ii) "the pins need only the radius restatement": under (R) the pins need no radius, but `GtoAG` needs the rooted twin (row G, ≈ 470), which is not a radius restatement and is not in the count of 2244 R3 (ii): this is the only new item; (iii) LW closes at 51 with LW-01 at 52 and no open mathematical item: yes in the three-row packing. LW crosses 50 at R2 and closes at R3, so the 50-line review applies to this report. Risk: observed overruns of the stop line were 1757/1500 (T2328, DECISIONS §147 (1)) and 3823/2200 (T2329, §148 (5)); at those factors two or three cuts are likely and LW-01 would be 54-55.

## 9. Risks, paper-delta candidates, open questions

* **Risk 1 (size of R1).** Central at the top of the supervisor's range; hi 2170. Cut C1 is named. **Risk 2 (rooted forest).** A copy of `auxGraph_exists_forest` with the roots as a hypothesis; if it snags, route (E) is the fallback (section 3) at the price of two cost factors and the clamp. **Risk 3 (G2 class facts).** `LWClass` for `Φ_E` (`W^{-d/2} ≤ C₃ Φ_E(0)`, `Φ_E ≤ W^{-ε₀}`) is checked only through (a) rows 4-6. **Risk 4 (bridge).** The weighted `|f|^p` bridge is stated in the table of section 8 but not compiled (the probe has 2 lines left of its 600). **Risk 5 (premise ledger).** The project audit `#assert_rbm_axioms` (`Test/Axioms.lean:483`), run with the probe imported (prove report (b) B6), passes its axiom step (`:504-514`) and stops at the premise classification (`:540-542`), listing `LWGtoAGRooted`, `LWEngineProv`, `LWExpData`: premises of probe theorems that no theorem proves. In merged code the first two are the pins of R3 and R1 and become theorems; `LWExpData` is not provable, so R1 must spell its nine conjuncts inline in `WExp`/`WExp.prod`, as `LWLocRegConcl` conjunct 4 does (`Graph/LWEngine.lean:68-75`), since `Test/Axioms.lean` is not among R1's writable files. **Not claimed.** The probe proves `WExp.refl`, `WExp.comp`, `WExp.prod`, `Molecular.comp`, `CoverBy.comp`, `lwEngineProv_imp_localregularX`, `gtoAGRooted_imp`, `LWf_split`, `norm_add3_pow_le`, `sum_ball_inf_min_pow_le`, `sfT_shift_le`, `lwTail32` and the instances; `LocStepXProv`, `LWEngineProv`, `LWGtoAGRooted`, `LWAuxNestedOwnOn`, `EKTTkInf`, `AnpNearInfAt`, `LWXiExpClaim`, `LWMomExpNoExp`, `LWMomExpFarPin`, `LWMomExpNearPin`, `LWMomentExpOfParts` are `Prop` definitions without proofs.
* **Paper-delta candidates** (O3 of supervisor 2244, `2244.md:63`; to be numbered by the dispatcher): `T2344a` (`7_8:1631-1648`: "all internal vertices lie in `D`" is the statement that the aux vertices are rooted at `π β^{(k)}`; Lean carries the weight on the initial `β^{(k)}` through the expansion, `WExp`, and uses the free centre of `7_8:860`); `T2344b` (`7_8:1607-1611`: `f = f^> + f^(a) + f^(b)`, "and" far domain, single-centre near domains); `T2344c` (`7_8:1653`, `7_8:95-97`: radius `(log W)^{3/2}`, the shift comparability replaces `(eq:Psi)`); `T2344d` (`7_8:1662`: `claim:TTk` in `ℓ^∞`, the paper's `|·|` is `L^∞`, `1_2:274`); `T2348a` (the cost of the cap shift needs `(ρ+1)^{(d-2)/2}`, probe 407); `T2348b` (`7_8:1602`: the scale `K (log W)^{3/2} ℓ_t` of regime (A) with a free constant `K`, because the expansion needs `|a-b| > K r`); `T2348c` (not a paper delta, a correction of the ticket and of supervisor 2244 O1: the de-privatisation list has 10 entries, not 2).
* **Open questions (for the REQ to the supervisor).** (1) Accept route (R) (rooted `GtoAG`, exact domains) instead of (E) (enlargement by `Rb`)? (2) Accept the three-row packing R1, R2, R3 and the cut names, LW-01 = 52? (3) Release R1 and R2 together (no shared file) after the PASS?

## 10. Script output

**B4 long statements** (run Fri Oct  9 00:40:26 UTC 2026; `python3 -I extract.py RBM3D/Probe/T2348Pins.lean LWEngineProv LWGtoAGRooted LWAuxNestedOwnOn LWMomentExpOn regA LWXiE`; the other statements are in `T2348-prove.md` (b) B3)
```
-- probe 164-170: LWEngineProv
 164| def LWEngineProv : Prop :=
 165|   ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
 166|     ∃ outs errs : List (ProvOutX (fxyPowGraph p).pack),
 167|       (∀ o ∈ outs ++ errs, o.ExtOK ∧ o.Cover p) ∧ ∀ m : ℂ, m ≠ 0 →
 168|         LWLocRegConcl p m c K0 d D ((outs.map (·.ev m)).map (·.Q)) ((errs.map (·.ev m)).map (·.Q)) ∧
 169|         (∀ Q ∈ ((outs ++ errs).map (·.ev m)).map (·.Q), p ≤ Q.g.waved.countP (fun e => !e.col)) ∧
 170|         WExp m (fxyPowGraph p).pack ((outs ++ errs).map (·.ev m))
-- probe 197-214: LWGtoAGRooted
 197| def LWGtoAGRooted (d : ℕ) : Prop :=
 198|   3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
 199|     (Γ : LGraph E I), Γ.Normal → (∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b) →
 200|     ∀ (rep : LGraph.AuxIMol Γ → I), (∀ c, Γ.molOf (Sum.inr (rep c)) = c.1) →
 201|     ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ) (Dm : Finset (Zd d L)),
 202|       (∀ x y, D.M x y = if x = y then m else 0) →
 203|       (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) → 0 ≤ C → 0 < c →
 204|       (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
 205|       (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
 206|       (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → 0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
 207|       (∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y → (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
 208|         (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y‖ ≤ ξ a b) →
 209|       ∀ (Wt : (E ⊕ I → Idx d L W) → ℝ), (∀ ℓ, |Wt ℓ| ≤ 1) →
 210|         (∀ ℓ, Wt ℓ ≠ 0 → ∀ c, (split d L W (ℓ (Sum.inr (rep c)))).1 ∈ Dm) → ∀ ℓe : E → Idx d L W,
 211|           ‖valW Γ D Wt ℓe‖ ≤
 212|             Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - LGraph.auxOrd Γ) *
 213|                 (((W : ℝ) ^ d) ^ Γ.nM * auxValOn Γ ξ (fun a => (split d L W (ℓe a)).1) Dm) +
 214|               Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L
-- probe 218-224: LWAuxNestedOwnOn
 218| def LWAuxNestedOwnOn : Prop :=
 219|   ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
 220|     Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
 221|     ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ lwMomExpFar_ownExt Γa ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
 222|       ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
 223|         ∀ Dm : Finset κ, Γa.valOn ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1))
 224|           (Fintype.piFinset fun _ : Fin Q.g.nM => Dm) = auxValOn Q.g ξ be Dm
-- probe 507-518: LWMomentExpOn
 507| def LWMomentExpOn (d : ℕ) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
 508|     (reg : ∀ (sz : Sizes d) (n : ℕ), ℝ → ℝ → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) → Prop) : Prop :=
 509|   3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
 510|     STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
 511|       ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
 512|         sz.Prec (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
 513|             sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ reg sz n (t n) (ℓ n) q})
 514|           (fun n q _ => ∫ ω, ‖LWfD sz n (STflowE z n) (t n) ω
 515|             (dom (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n)) q.1.1 q.1.2‖ ^ p ∂(sz.seqP))
 516|           (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
 517|             sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
 518|               (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))
-- probe 521-524: regA
 521| def regA (d : ℕ) (K : ℝ) (sz : Sizes d) (n : ℕ) (t ℓ : ℝ) (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : Prop :=
 522|   ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ) ≤
 523|       K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t ∨
 524|     ℓ ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t
-- probe 446-452: LWXiE
 446| def LWXiE {d : ℕ} (sz : Sizes d) (E t ℓ : ℕ → ℝ) (D : ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
 447|   (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
 448|     sz.Prec (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω)
 449|       (fun n p _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
 450|         (min ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
 451|     sz.Prec (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
 452|       (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (E n) (t n))⁻¹)
-- total lines printed: 55
```

**B5 sizes of the sources that each piece twins, and the row estimates** (run Fri Oct  9 00:40:32 UTC 2026; scripts `decls.py`, `rows.py`, spec `spec.json` in the scratch directory; code lines = non-blank, non-comment lines from the declaration line to the next top-level declaration)
```
$ python3 -I decls.py <worktree> spec.json | grep "^##\|group total"
## P1 partition (value level, weighted twins)
  group total (code lines) = 136
## P2 expansion identities and packing (LWLvl1)
  group total (code lines) = 181
## P3 twist wrappers (LWSymm)
  group total (code lines) = 213
## P4 graph-level sums over the labels (the `ℓi` sum is taken after the term lemma)
  group total (code lines) = 241
## P5 the recursion on the carrier (LWEngine)
  group total (code lines) = 161
## P6 weighted `|f|^p` bridge (the source is `fxyPowGraph_val_eq` + `lwMoment_fxyPow_val`)
  group total (code lines) = 48
## G rooted GtoAG
  group total (code lines) = 332
## M the ell^inf near chain
  group total (code lines) = 452
## X G2 and the tail
  group total (code lines) = 369
## F the expansion argument of lwMoment_holds (exp analogue)
  group total (code lines) = 568
## A the no-exp regime (analogue: T2342 `LWTermExpN.lean`)
  group total (code lines) = 271
## totals {"P1 partition (value level, weighted twins)": 136, "P2 expansion identities and packing (LWLvl1)": 181, "P3 twist wrappers (LWSymm)": 213, "P4 graph-level sums over the labels (the `\u2113i` sum is taken after the term lemma)": 241, "P5 the recursion on the carrier (LWEngine)": 161, "P6 weighted `|f|^p` bridge (the source is `fxyPowGraph_val_eq` + `lwMoment_fxyPow_val`)": 48, "G rooted GtoAG": 332, "M the ell^inf near chain": 452, "X G2 and the tail": 369, "F the expansion argument of lwMoment_holds (exp analogue)": 568, "A the no-exp regime (analogue: T2342 `LWTermExpN.lean`)": 271}
$ python3 -I decls.py <worktree> spec.json | grep "val_eq_merge_val  \|lwEngine_exists  \|lwGtoAG_holds  \|LocStepX.eval"
  RBM3D/Graph/LWVocab.lean:881-934  LGraph.val_eq_merge_val  code lines = 54
  RBM3D/Graph/LWEngine.lean:667-720  lwEngine_exists  code lines = 54
  RBM3D/Graph/LWEngine.lean:418-444  LocStepX.eval  code lines = 27
  RBM3D/Graph/AuxGraph.lean:1018-1127  lwGtoAG_holds  code lines = 110
$ cd <worktree>; for r in "Graph/LWVocab.lean 881 934" "Graph/LWEngine.lean 667 720" "Graph/AuxGraph.lean 1018 1127"; do set -- $r; sed -n "$2,$3p" RBM3D/$1 | grep -vc "^[[:space:]]*$"; done
54
54
110
$ python3 -I rows.py <worktree> spec.json decls.py   # bases = the code lines above; P1-P5 base 905 = 932 - 27 (LocStepX.eval is reused as it is); P6 base 29 = fxyPowGraph_val_eq + lwMoment_fxyPow_val
## P  provenance engine (Graph/LWProv.lean)
   weighted twins of P1-P5 (base 905)                                                                724   996  1448
   weighted |f|^p bridge (base 29)                                                                    29    44    72
   maps: ExtOK / Molecular / Cover lemmas (new)                                                      150   250   400
   statements, docstrings, instances, registry                                                       100   150   250
   row total (lo / central / hi)                                                                    1003  1440  2170
## G  rooted GtoAG + restricted aux identity (Graph/AuxGraphRooted.lean)
   rooted forest (base 79)                                                                            79    87   118
   main sum with indicator (base 68)                                                                  68    88   122
   GtoAG twin (base 110)                                                                             110   132   187
   restricted aux identity (base 63)                                                                  63    76   107
   valW glue, statements, instances                                                                   60    90   150
   row total (lo / central / hi)                                                                     380   473   684
## M  claim:TTk and near pin in l^inf (Graph/LWMomExpInf.lean; keyword-only edit of LWMomExp.lean:310,434)
   kernel pair lemmas (base 91)                                                                       91   109   146
   key_T_reduce (+absorbed) (base 110)                                                               110   132   176
   l^inf ball sum, compiled in the probe (new)                                                        40    50    80
   ekTTkInf wrapper (base 15)                                                                         15    20    30
   near chain wrappers (base 159)                                                                    159   191   270
   tau/def block (LWMomExp.lean:521-565, base 45)                                                     45    54    68
   statements, instances                                                                              60    90   150
   row total (lo / central / hi)                                                                     520   646   920
## X  G2 exp-class xi, (log W)^{3/2} tail, (A) (Graph/LWXiExp.lean, Graph/LWMomentExpA.lean)
   G2 twin of lwXiClaim_holds (base 133)                                                             120   160   226
   shift comparability for tailW, Kn <= N^tau, class facts (new)                                     120   180   300
   tail copy (base 34; compiled in the probe)                                                         34    44    54
   (A): twin of lwtermExpN_of_LWterm (base 96), new regime algebra                                   288   403   624
   statements, instances                                                                             100   140   220
   row total (lo / central / hi)                                                                     662   927  1424
## F  expansion argument, split, assembly, registry (Graph/LWMomentExp.lean, Test/Axioms.lean)
   expand + int + far_r + far (base 154)                                                             154   200   277
   scale (base 70)                                                                                    70    84   112
   anp (base 185)                                                                                    185   240   333
   err (base 45)                                                                                      45    54    72
   floor for the exp RHS (base 86)                                                                    69    86   129
   Prec union, split, W^{-D} floor edges, lwMomentExp_of_parts (new)                                 180   280   480
   statements, instances, registry                                                                   100   150   250
   row total (lo / central / hi)                                                                     803  1094  1653
## packings (lo / central / hi)
R1 = P                                    1003  1440  2170
R2 = M + X                                1182  1573  2344
R3 = G + F                                1183  1567  2337
all five pieces                           3368  4580  6851
4-row: P | G + M | X | F: G+M              900  1119  1604
4-row: X                                   662   927  1424
4-row: F                                   803  1094  1653
```

**B6 the de-privatisation list of the `ℓ^∞` twin, and the generic chain** (run Fri Oct  9 00:40:33 UTC 2026)
```
$ python3 -I privs.py RBM3D/Graph/LWMomExp.lean
private declarations of the file: 48
copied in the twin (defined inside the twin segments): 13
private declarations referenced by the twin and defined outside it (keyword-only de-privatisation list):
  Graph/LWMomExp.lean:152  lwMomExp_chain_nonneg
  Graph/LWMomExp.lean:310  lwMomExp_step_aux
  Graph/LWMomExp.lean:434  lwMomExp_sys_bound
  Graph/LWMomExp.lean:752  lwMomExp_walk_chain
  Graph/LWMomExp.lean:835  lwMomExp_path_ne
  Graph/LWMomExp.lean:846  lwMomExp_sysOf_length
  Graph/LWMomExp.lean:851  lwMomExp_sysOf_mem
  Graph/LWMomExp.lean:862  lwMomExp_pathEdges
  Graph/LWMomExp.lean:874  lwMomExp_pathEdges_card
  Graph/LWMomExp.lean:882  lwMomExp_prod_split
closure (needed by the above, defined outside the twin segments):
  Graph/LWMomExp.lean:64  lwMomExp_fm_some
  Graph/LWMomExp.lean:67  lwMomExp_fm_none
  Graph/LWMomExp.lean:74  lwMomExp_marks
  Graph/LWMomExp.lean:161  lwMomExp_base
  Graph/LWMomExp.lean:218  lwMomExp_sum_succ
  Graph/LWMomExp.lean:248  lwMomExp_phi_none
  Graph/LWMomExp.lean:256  lwMomExp_phi_succ
  Graph/LWMomExp.lean:265  lwMomExp_psi
  Graph/LWMomExp.lean:268  lwMomExp_lab_cons
  Graph/LWMomExp.lean:277  lwMomExp_prod_flatten
  Graph/LWMomExp.lean:282  lwMomExp_prod_fin
  Graph/LWMomExp.lean:287  lwMomExp_length_flatten
  Graph/LWMomExp.lean:292  lwMomExp_psi_isNone
  Graph/LWMomExp.lean:414  lwMomExp_del_length
  Graph/LWMomExp.lean:710  lwMomExp_stepFn
  Graph/LWMomExp.lean:715  lwMomExp_stepFn_eq
  Graph/LWMomExp.lean:729  lwMomExp_foldl_none
  Graph/LWMomExp.lean:736  lwMomExp_fold_cons
  Graph/LWMomExp.lean:782  lwMomExp_walk_last
  Graph/LWMomExp.lean:802  lwMomExp_walk_visit
  Graph/LWMomExp.lean:842  lwMomExp_path_split
  Graph/LWMomExp.lean:865  lwMomExp_pathEdges_disj
zdist occurrences in the generic chain lines 304-516: 0
zdist occurrences in 304-516 (list): []
$ sed -n 304,516p RBM3D/Graph/LWMomExp.lean | grep -c zdist
0
```

**B7 echo of every citation of this report** (run Fri Oct  9 00:40:33 UTC 2026; `python3 -I echo_cites.py T2348-design.md`: for each citation of sections 0-9 the first 36 characters of the cited line, both ends of a range; `probe N` is line N of `RBM3D/Probe/T2348Pins.lean` at commit 9f3bd75; Lean paths are relative to `RBM3D/` at the base `692a72b` of the branch; `paper 7_8` / `paper 1_2` are `paper/tex/7_8_light_weight.tex` / `1_2_Intro_model_result.tex`)
```
probe: 34 «def valW {E I : Type} [Fintype I] [D» | 64 «def ProvOut.Molecular {P : PGraph (F» | 69 «def LWExpData {d : ℕ} (sz : Sizes d)» | 77 «def WExp (m : ℂ) (P : PGraph (Fin 2)» | 77-170 «def WExp (m : ℂ) (P : PGraph (Fin 2)» .. «WExp m (fxyPowGraph p).pack ((outs +» | 88 «theorem ProvOut.Molecular.comp {P : » | 96 «theorem WExp.refl (m : ℂ) (P : PGrap» | 101 «theorem WExp.comp {m : ℂ} {P : PGrap» | 111 «theorem WExp.prod {m : ℂ} {p : ℕ} {o» | 125 «theorem CoverBy.comp {P : PGraph (Fi» | 157 «def LocStepXProv : Prop :=» | 164 «def LWEngineProv : Prop :=» | 173 «theorem lwEngineProv_imp_localregula» | 189 «def auxValOn {E I : Type} [Fintype E» | 189-227 «def auxValOn {E I : Type} [Fintype E» .. «theorem gtoAGRooted_imp (h : LWGtoAG» | 197 «def LWGtoAGRooted (d : ℕ) : Prop :=» | 218 «def LWAuxNestedOwnOn : Prop :=» | 227 «theorem gtoAGRooted_imp (h : LWGtoAG» | 248-320 «def domFar (a b : Zd d L) (ℓ : ℝ) : » .. «» | 262 «theorem domFar_eq {p : ℕ} (hp : 0 < » | 292 «def LWfD {d : ℕ} (sz : Sizes d) (n :» | 313 «theorem LWf_split {d : ℕ} (sz : Size» | 322 «theorem norm_add3_pow_le (a b c : ℂ)» | 335 «def EKTTkInf (d n : ℕ) : Prop :=» | 335-394 «def EKTTkInf (d n : ℕ) : Prop :=» .. «» | 346 «def AnpNearInfAt (d : ℕ) {p q : ℕ} (» | 358 «theorem sum_ball_inf_min_pow_le {L :» | 396 «theorem sqrt_le_add_sqrt_shift {s ρ » | 396-470 «theorem sqrt_le_add_sqrt_shift {s ρ » .. «((sz.size n : ℕ) : ℝ) ^ (-b) := by» | 407 «theorem sfT_shift_le {d L : ℕ} {W g » | 446-463 «def LWXiE {d : ℕ} (sz : Sizes d) (E » .. «LWXiE sz (STflowE z) t ℓ D (lwXiVar » | 467 «theorem lwTail32 {d : ℕ} (sz : Sizes» | 507 «def LWMomentExpOn (d : ℕ) (dom : ∀ (» | 507-538 «def LWMomentExpOn (d : ℕ) (dom : ∀ (» .. «∀ K : ℝ, LWMomExpNoExp d K → LWMomEx» | 521 «def regA (d : ℕ) (K : ℝ) (sz : Sizes» | 527 «def LWMomExpNoExp (d : ℕ) (K : ℝ) : » | 529-534 «def LWMomExpFarPin (d : ℕ) (K : ℝ) :» .. «LWMomentExpOn d (fun L _ a b ℓ => do» | 537 «def LWMomentExpOfParts (d : ℕ) : Pro» | 565 «example : AnpFarAndAt 3 figAux := lw» | 581 «example : ∑ α : Zd (1 + 2) 5, ((min » | 591 «example : ∀ᶠ n in atTop, Real.exp (-»
paper 7_8: 95-97 «The remainder of this section is dev» .. «|a-b| > (\log W)^{3/2}.» | 351 «Corresponding to the three lemmas ab» | 860 «More precisely, for each internal mo» | 1602 «Note that when $|a-b|\le (\log W)^{3» | 1607-1611 «\begin{align*}» .. «\Gc_{\beta\beta} G_{x\al }G_{\al y}.» | 1631-1648 «\begin{proof}[\bf Proof of \Cref{lem» .. «Next, we bound each locally standard» | 1633 «We then estimate the auxiliary graph» | 1637-1638 «In the proof of \Cref{lem:Anp_key_gh» .. «Each such long edge provides a facto» | 1648 «Next, we bound each locally standard» | 1653 «We first control \smash{$\cal G^{\au» | 1662 «Assume $1-t\ge \ilambda^2/L^{2}$. Th»
RBM3D/Graph/LWMomExp.lean: 152 «private theorem lwMomExp_chain_nonne» | 304-516 «section Step» .. «end Induction» | 310 «private theorem lwMomExp_step_aux (w» | 434 «private theorem lwMomExp_sys_bound (» | 521 «noncomputable def lwMomExp_tau (d L » | 521-581 «noncomputable def lwMomExp_tau (d L » .. «end Tau» | 532 «noncomputable def lwMomExp_nearD (d » | 584-593 «private def lwMomExp_TTkBody (d n : » .. «∏ i, sfT d L W g t (min (zdistD d L » | 584-699 «private def lwMomExp_TTkBody (d n : » .. «(mul_nonneg hK.le hZ) (lwMomExp_hste» | 752 «private theorem lwMomExp_walk_chain » | 835 «private theorem lwMomExp_path_ne (hN» | 846 «private theorem lwMomExp_sysOf_lengt» | 851 «private theorem lwMomExp_sysOf_mem (» | 862 «private def lwMomExp_pathEdges : Fin» | 874 «private theorem lwMomExp_pathEdges_c» | 882 «private theorem lwMomExp_prod_split » | 900 «def AnpDetNearAt (d : ℕ) {p q : ℕ} (» | 918-1024 «private theorem lwMomExp_nSolid (Γ :» .. «fun d hd _ _ Γ hNG hN => lwMomExp_ne» | 1023 «theorem lwMomExp_near : ∀ d, AnpDetN»
T2348.md: 7 «2. **Molecule-level domain pins.** E» | 12 «7. **Rows:** the proving rows with s»
2244.md: 28 «- **Downstream side.** `GtoAG` / the» | 42 «- TEAM §6's 50-line HOLD exists to f» | 55 «| LW | 47 (T2344 at 1a) | **51–52** » | 63 «- **O3 (R2).** Record paper-deltas T»
T2344-prove.md: 23 «| 11 | **G2** edge variables of the »
RBM3D/Graph/LWEngine.lean: 57 «def lwEvX (m : ℂ) (r : (ℕ × ℕ) × PGr» | 66 «Q.g.Normal ∧ (fxyPowGraph p).pack.g.» | 68-75 «(∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u» .. «(errs.map fun Q => ∫ ω, Q.val (lwSam» | 178 «theorem lwEngine_blk_nat (m : ℂ) (t0» | 391 «inductive LocStepX : PGraph (Fin 2) » | 392 «| weight (P : PGraph (Fin 2)) (p : S» | 395 «| edge (P : PGraph (Fin 2)) (p : SEd» | 400 «| gg (P : PGraph (Fin 2)) (p q : SEd» | 418 «theorem LocStepX.eval {P : PGraph (F» | 560 «theorem lwEngine_locStep_nWS {E : Ty» | 628 «theorem lwEngine_combine {E : Type} » | 654 «theorem lwEngine_flat_eval (m : ℂ) (» | 667 «theorem lwEngine_exists (K : ℤ) (Γ :» | 771 «theorem lw_localregularX :»
RBM3D/Graph/LWLvl1.lean: 3105 «theorem PGraph.lvl1Comp_val (Q : PGr» | 3228-3249 «def lvl1WeightOuts0 {E' I' : Type} [» .. «(lwSplit q.2).flatMap (fun q' => (lw» | 3236 «def lvl1EdgeOuts0 {E' I' : Type} [Fi» | 3243 «def lvl1GGOuts0 {E' I' : Type} [Fint» | 3252 «def lvl1Pack (P : PGraph E) (L : Lis» | 3373 «theorem lvl1_val_zero_of_xself {ι : » | 3389 «theorem lvl1_oe1xT1_zero {ι : Type*}» | 3408 «theorem lvl1_oe2xR1_zero {ι : Type*}» | 3450 «theorem lvl1_pack_identity {E : Type» | 3590 «theorem lvl1_step_identity {E : Type»
RBM3D/Graph/AuxGraph.lean: 79 «def LGraph.auxVal {κ : Type} [Fintyp» | 459 «theorem auxGraph_exists_forest (Γ : » | 459-537 «theorem auxGraph_exists_forest (Γ : » .. «· exact hne (Sum.inr_injective (a1.s» | 476 «choose rootI hroot using hMi» | 663 «theorem auxGraph_sum_blocks {Rt : Ty» | 798 «theorem auxGraph_tail_sum (hd : 3 ≤ » | 901 «theorem auxGraph_main_sum (hd : 3 ≤ » | 936-968 «set Φ : (LGraph.AuxIMol Γ → Idx d L » .. «_ ≤ _ := hmain» | 979 «def LWGtoAG (d : ℕ) : Prop :=» | 991-993 «(∀ (x y : Idx d L W) (a b : Zd d L),» .. «‖D.G x y‖ ≤ ξ a b) →» | 1018 «theorem lwGtoAG_holds (d : ℕ) : LWGt» | 1078 «have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.» | 1115-1127 «unfold LGraph.val» .. «_ ≤ _ := add_le_add hmain' htail» | 1526 «theorem auxGraph_val_eq (hxy : Q.g.m»
RBM3D/Graph/LWMomExpFar.lean: 16-18 «Corrected statement (supervisor 1102» .. «`𝖳_t(|a_i - b_i|_∞ ∧ ℓ)` (a path wit» | 42 «def lwMomExpFar_farDAnd (d L : ℕ) [N» | 57 «def lwMomExpFar_HeadFar (d L : ℕ) [N» | 80 «def AnpFarAndAt (d : ℕ) {p q : ℕ} (Γ» | 80-89 «def AnpFarAndAt (d : ℕ) {p q : ℕ} (Γ» .. «∏ i, sfT d L W g t (min ((zdistInf d» | 96 «def LWAuxNestedOwn : Prop :=» | 338 «theorem lwMomExpFar_and : ∀ d : ℕ, A»
RBM3D/Graph/LWPins.lean: 199 «def LWf (n : ℕ) (E t : ℝ) (ω : sz.Se» | 283 «def LWAssmExp (E t : ℕ → ℝ) (ε₀ : ℝ)» | 341 «def LWMomentExp (d : ℕ) : Prop :=» | 360 «def LWXi (E t : ℕ → ℝ) (Φ : ℕ → ℝ → »
RBM3D/Test/Axioms.lean: 160 «`RBM.Gauss.Sizes.LWMomentExp, -- `le» | 483 «elab "#assert_rbm_axioms" : command » | 504-514 «let permitted := allowedAxioms ++ in» .. «throwError m!"axiom audit failed:\n{» | 540-542 «let unregistered := found.filter fun» .. «throwError m!"axiom audit: {unregist»
RBM3D/Graph/AuxGraph2.lean: 723 «private theorem auxGraph2_phi_cmp {Φ» | 951 «def LWXiClaim (d : ℕ) : Prop :=» | 965 «theorem lwXiClaim_holds (d : ℕ) : LW» | 965-1098 «theorem lwXiClaim_holds (d : ℕ) : LW» .. «linarith» | 1019 «have hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m» | 1019-1021 «have hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m» .. «exact auxGraph2_phi_cmp (Φ := Φ n) (» | 1114 «∀ ρ R : ℕ → ℝ, (∀ n, 0 ≤ R n) → (∀ n»
RBM3D/Graph/LWMoment.lean: 473 «theorem lwMoment_tail (S : LWMomentC» | 925 «theorem lwMoment_prec_scale (S : LWM» | 1034-1038 «theorem lwMoment_prec_anp (S : LWMom» .. «(hord : (2 * p : ℤ) ≤ Q.g.scalingOrd» | 1048 «let Rb : ℕ → ℝ := fun n => (K : ℝ) *» | 1748 «theorem lwMoment_fxyPow_val {p : ℕ} » | 1785 «theorem lwMoment_holds : ∀ d : ℕ, LW» | 1810-1812 «by_cases hq : (K : ℝ) * Real.log ((s» .. «· exact h2 ⟨q, le_of_not_gt hq⟩»
RBM3D/Graph/LWWeightExp.lean: 454 «def owxEmb (k : ℕ) : E ⊕ I → E ⊕ (I » | 458 «def LGraph.owxExt {E' I' : Type*} (Γ» | 591 «theorem owxExt_nM (Γ : LGraph E I) (» | 705 «theorem owxExt_reach1 (Γ : LGraph E » | 1046 «theorem owxLab1_emb {ι : Type*} (ℓe » | 1060 «theorem owx_term_integral (hG : Gaus» | 1333 «have hL : ∫ ω, Γ.val (lwSampleData s» | 1339 «simp_rw [owx_term_integral hG hz hu »
RBM3D/Graph/LWSymm.lean: 232 «theorem lwSymm_term_conj (D : LData » | 246 «theorem lwSymm_term_transpose (D : L» | 465 «theorem lwSymm_integral_flip (sz : S» | 558 «theorem lwSymm_twist_integral (hSr :» | 1174 «have hL : ∫ ω, Γ.val (lwSampleData s» | 1180 «simp_rw [owxE_term_integral hG hz hu» | 1418 «theorem lwSymmUncirc_term (D : LData» | 1590 «theorem lwSymm_weight_graph_E (hG : » | 1639 «theorem lwSymm_oe1x_graph_E (hG : Ga» | 1690 «theorem lwSymm_oe2x_graph_E (hG : Ga»
RBM3D/Graph/LWEdgeExp.lean: 606 «def oe1xD (m : ℂ) (Γ : LGraph E I) (» | 654 «theorem oe1x_term_integral (hG : Gau» | 827-828 «rw [hval Γ, hval (oe1xT1d m Γ p x v)» .. «simp_rw [oe1x_term_integral hG hz hu» | 863 «def oe1xT1 (m : ℂ) (Γ : LGraph E I) » | 1084-1116 «def oe1xP5 (m : ℂ) (Γ : LGraph E I) » .. «[⟨false, true, Sum.inr (Sum.inl x), » | 1123 «theorem oe1xD_red_term (D : LData ι)» | 1269-1279 «have hsplit : ∀ (A B : LGraph E (I ⊕» .. «simp only [LGraph.val, ← Finset.sum_»
RBM3D/Graph/LWGGExp.lean: 485 «def oe2xR2 (m : ℂ) (Γ : LGraph E I) » | 560 «def oe2xPhi (x : I) (y : E ⊕ I) (hy » | 1243 «theorem oe2x_term_integral (hG : Gau» | 1574-1614 «have hL : ∫ ω, Γ.val (lwSampleData s» .. «simp_rw [oe2x_term_integral hG hz hu»
RBM3D/Graph/LWVocab.lean: 157 «def LGraph.adj (Γ : LGraph E I) (u v» | 768 «def LGraph.vmap (Γ : LGraph E I) (v » | 850 «private theorem LGraph.term_merge (Γ» | 881 «theorem LGraph.val_eq_merge_val (Γ :» | 884 «set Φ : (Γ.IntCls → ι) → (I → ι) := » | 885 «have hlab : ∀ ℓi', Sum.elim (ℓ' ∘ Γ.» | 906 «have hrange : ∀ ℓi : I → ι, ℓi ∉ Set» | 938 «theorem LGraph.mergeP_val (Γ : LGrap» | 1168 «theorem LGraph.term_eq_sum_dotChoice» | 1253-1260 «have hterm : ∀ ℓ : E ⊕ I → ι,» .. «ring»
RBM3D/Graph/LocalRegular.lean: 1354 «def fxyPowGraph (p : ℕ) : LGraph (Fi»
T2289-prove.md: 96 «3. *Domain through `a_1` (S1): posit»
RBM3D/Defs/Tail.lean: 119 «theorem zeroMode_le_of_ge (hd : 2 ≤ »
RBM3D/Evolution/Pins.lean: 156 «def EKTTk (d n : ℕ) : Prop :=»
RBM3D/Defs/RadialSum.lean: 367 «theorem sum_ball_min_pow_le (k : ℕ) »
RBM3D/Defs/Sizes.lean: 122 «theorem zdistD_le_mul_zdistInf (d L »
RBM3D/Kernel/PropT.lean: 788 «theorem sfT_pair_le (hW : 0 < W) {ℓ » | 839 «theorem prod_sfT_pair_le (hW : 0 < W» | 913 «theorem key_T_reduce (hW : 0 < W) {k» | 1056 «theorem key_T_reduce_absorbed {L : ℕ»
RBM3D/Graph/AnpKey.lean: 101 «theorem anpKey_zdistInf_tri (x y z :»
RBM3D/Graph/LWTermExpN.lean: 414 «theorem lwtermExpN_of_LWterm (d : ℕ)»
paper 1_2: 274 «For definiteness, we use the $L^\inf»
-- 224 citations, 197 distinct, in 29 files; missing lines: 0
```
