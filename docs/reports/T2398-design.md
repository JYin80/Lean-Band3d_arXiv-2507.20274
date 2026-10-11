W2: NO (the band term bounds `LWExpI1K`, `LWExpI23K`, `LWExpI41K`, `LWExpTerm2.lean:81, 96, 115`, do not instantiate at the BA term list: it has no `E_a`-loop form, §2; L4a becomes a twin, L4a2 is unchanged). W3: C (direct proof of `(eq:sizeGammamu_E)` for `𝒢_xy`, in the corrected averaged form `ord ≥ 5 − 2·1[x ~ y]`: the paper's pointwise form is false at BA, compiled; L4e1–L4f2, 4,854 central lines and the 31–93 min lane slot, are replaced by one row). STOP: (v) of `B:118` is not closable from the paper and the merged or pinned inputs, one missing step (family `T3C-Ḡ`, the BA `I₄₁`, §8): RETURN with one question to Jun.

Prover `claude-sonnet-5-5` (prover-max, design only). Branch `t/T2398` (base `1a5f972`), probe `RBM3D/Probe/T2398Pins.lean` (399 lines, limit 400), commits `2e23b9f`, `e32530a`, `5f96301`, `5c62eb7`, `fdc8c57`, `2257f54`. Last edit: Sun Oct 11 00:08:18 UTC 2026 (`date -u`).
Citations: `B:N` = `paper/tex/B_graphical_lemmas.tex`; `path:N` is relative to `RBM3D/` at the base; `probe N` is a line of the probe; `(a) row k` is row k of the exponent table in `docs/reports/T2398-prove.md`; `T2387 §k` is `docs/reports/T2387-design.md`.
Scripts are in the scratchpad subdirectory `T2398/` (not in the repository): `eng.py` (BA expansion engine), `g5.py`, `pointwise.py`, `tree5.py`, `parents.py`, `lemma_final.py`, `family.py`, `elw.py` with `elw_summary.py`, `regen.py`, `mc_gg.py`, `twist.py`, `crude.py`, `kern.py` (their output is in (b)); `num.py`, `d402.py` are the preflight's (output in (a)). The engine models counters `(n_S, n_W, n_A)`, atoms and molecules of BA graphs and the rules `B:361-405`: a model of the term lists, not a proof (limits, §8).

## 0. The answer

| item | answer | where |
|---|---|---|
| W1 | At BA `S^{(B)} = I` (`B:289`): `(eq:ELW_term)` (`B:11-14`) has `a₂ = a₁`. After `G = Ǧ + M` (`B:342`) the pair `G_{xα}G_{αy}` is `ǦǦ + MǦ + ǦM + MM`. `GGGamma` (D402) on `ǦǦ` gives 47 first-level graphs (`family.py`) (`T1`, `T2a`, `T2b`, `T3A_k`, `T3B_k`, `T3C_k`, `k = 0, 1`); `MǦ`, `ǦM` need `lanlw`. The band's `I₁…J₄` correspond to `{MM, T1, T2, MǦ, ǦM}`, `T3A`, `T3B`, `T3C-Ḡ`, `T3C-tr`. Kernel `ω = (1 − tM⁺_B)⁻¹` with `M^{(B)}` ties, not `S^{(B)}(m + m³K⁺)`. **No** step turns the `I₁` analogue into a `𝓛^{(2)}` | §1 |
| W2 | **No.** Two `M` edges give loop-free offset-tied sums (`MM`, `T1`); one `M` edge gives an *offset-twisted* loop (block jump `M^{(B)}_{c₁c₂}`); `FlowFM` (`Chain/Carrier.lean:55-71`) has only `E_a`-loops. The BA statements live at the fine level (`BAlwData`) | §2 |
| W3 | **C.** Pointwise `(eq:sizeGammamu_E)` is false at BA (`ba_pointwise_fails`, probe 56). Corrected target `ord ≥ 5 − 2·1[x ~ y]`. A lemma (`GGGamma` raises `ord` by ≥ 1 under three atom conditions, `T1` by 0 otherwise) and a closure table: 320 normal terms, 9 expanded, depth ≤ 2, 1,714 leaves, the three checked leaf properties hold. No certificate model | §3 |
| W4 | `baG5Graph`, `BAG5Identity` (probe 135-153); the engine `expandG_sum` is reused as is (weight `fun _ => 1`); D402 `W − 1 = M⁺SW` compiled (`ba_W_sub_one`, probe 119) and checked in expectation by Monte Carlo (the full identity, two `f`) | §4 |
| W5 | Compiled: L4d, L4e-C (`BAG5Leaf`, `BAG5Expand`), L4c joined (`BAGraphPrecJoin`), the common target `BALWCutExp` with an instance, the missing input `BATwistLaw`. Text pins: the L4a, L4b families and the `q = 1` leaf bound (conditional on §8 and stage G). Hypotheses: stage G `BAGbEXPij'`, `BAGbEXPii`, `BAGbEXPav`; K12 `STKwardgL`; the Step 1/2 pins of `Chain/Carrier` | §5 |
| C1/L5 | Constants at `g = 1/64, 1, 10`: count constant `g² + 1 = 1.0002, 2, 101`; kernels uniform; no `g ≤ W^{-ε}`, no `‖M − m₀I‖` small. The twisted kernel is **not** small at `g ≍ 1` (ratio `0.003, 4.255, 3.905`) | §6 |
| Rows | L4 under C and the twins: 9 rows (was 10), central 10,610 (was 13,513), no heavy lane slot; **conditional** on §8 | §7 |

## 1. W1: the BA term list

**1.1 The term.** `Λ_σ(a,b) := W^{-2d} Σ_{a₁} Σ_{x∈[a], y∈[b], α∈[a₁]} 𝔼[ tr(Ǧ E_{a₁}) · G_{yx}(σ) G_{xα} G_{αy} ] ≺ η_t^{-1}(W^{-d}B_{t,0})^{5/2}` (`B:11-14`, `σ = −`, `G_{yx}(−) = Ḡ_{xy}`).
It is `LWcutg` of `baFMz` (`Chain/LWGen.lean:39`: `W^d Σ_{a₁,a₂} C.S_{a₁a₂}(𝓛^{(1)} − m) 𝓛^{(3)}` with `C.S = 1`, `BA/FlowPins.lean:322-330`).
As a graph (`elw.py`, `family.py`): external `x, y`; internal `x'` with the weight `Ǧ_{x'x'}` and the waved edge `S_{x'α}`; solid `G_{xα}, G_{αy}, Ḡ_{xy}`; the all-circled term has `ord = 2`.

**1.2 Expansion.**
- `G = Ǧ + M` on the three edges (`baSplitSolid`, `BAVocab.lean:163`): 8 normal terms.
- `ǦǦ` at `α` by `GGGamma` (`B:393-405`, D402: the first two sums carry `(W − 1)_{αβ} = (M⁺S⁺)_{αβ}`, `W = 1 + M⁺S⁺ = (1 − M⁺S)⁻¹`) with `y' = x`, `y = y`, `f = tr(ǦE_{a₁}) Ḡ_{xy}`.
- `MǦ`, `ǦM`: `lanlw` (`B:361-372`; merged `baLanlw_holds`, `BAExpand.lean:744`, tail form) on the single `Ǧ`; for `ǦM` the tail is the external `x`, or the transposed form at `α` (not merged). `MM`: nothing to expand.

First-level graphs of the all-circled term (`family.py`, 47 in all; parent `ord = 2`, target 5, or 3 if `x ~ y`):

| family | expression (`f = tr Ḡ_{xy}`) | # | `ord` | band | route |
|---|---|---|---|---|---|
| `MM` | `M_{xα}M_{αy} f` | 1 | 1-2 | `I₁` (`mδ`) | loop-free: `x, α, y` in one atom, `W^d` pairs; `|𝔼 tr| ≺ B²` (band `STExpAvgAt`), `|Ǧ*_{xy}| ≺ Ψ`; `W^{-d}B² ≤ (g²+1)Ψ B^{5/2}` |
| `MǦ`, `ǦM` | `M_{xα}Ǧ_{αy} f`, `Ǧ_{xα}M_{αy} f` | – | 2-3 | `I₁` | twisted 2-loop `× tr`; expected after one `lanlw` (not verified): two weights (crude), `∂tr` (graph `𝒢` with an `M` edge), `∂Ḡ_{xy}` (standard `𝓛^{(2)}`, tied entries) |
| `T1` | `Σ_β (W−1)_{αβ} M_{βy}M_{xβ} f` | 1 | 2 (Δ = 0) | `J₁` | loop-free as `MM`; `(W−1)_{αβ} = W^{-d}𝒦̃_{[α][β]}` |
| `T2a`, `T2b` | `Σ_β (W−1)_{αβ} Ǧ_{βy} M_{xβ} f`, `…M_{βy}Ǧ_{xβ}…` | 1 + 1 | 3 | `J₁` | twisted 2-loop `× tr` (as `MǦ`) |
| `T3A_k` | `W_{αw}M_{wγ}S_{γδ} Ǧ_{δδ}G_{γy}Ǧ_{xw} f` | 2 + 2 | 3-4 | `I₂`, `J₂` | two weights `tr · tr(Ǧ E_{[γ]})`: expected crude + Ward as `I₂` (`B:43-47`), not verified |
| `T3B_k` | `W_{αw}M_{wγ}S_{γδ} Ǧ_{γw}G_{δy}G_{xδ} f` | 4 + 4 | 3-4 | `I₃`, `J₃` | the weight `Ǧ_{γw}M_{wγ}` is a twisted one-loop; expected after one `lanlw`: two weights (not verified) |
| `T3C-tr_k` | `−W_{αw}M_{wγ}S_{γδ} G_{δy}Ǧ_{xw} ∂_{h_{δγ}}(tr) · Ḡ_{xy}` | 8 + 8 | 3-6 | `I₄₂`, `J₄₂` | graph `𝒢^{BA}`: §3 (lever C) |
| `T3C-Ḡ_k` | `tr · Ǧ_{xw}M_{wγ}Ḡ_{xγ} · G_{δy}Ḡ_{δy}` (with `W_{αw}S_{γδ}`) | 8 + 8 | 3-5 | `I₄₁`, `J₄₁` | **twisted 2-loop × `tr` × `𝓛^{(2)}`: stuck (§8)** |

`k = 0` is the identity of `W`, `k = 1` its `S⁺` chain (`LWExpTerm2.lean:44-47`: `I_i` and `J_i`). The `T3C` row is split by the differentiated factor (`family.py`: 8 + 8 terms per `k`).
Reading of the band's eight terms: `J₁ ↦ T1, T2a, T2b` (kernel `W − 1`); `I₁ ↦ MM, MǦ, ǦM` (the `1` of `W`, from the split); `I₂, J₂ ↦ T3A_0, T3A_1`; `I₃, J₃ ↦ T3B_0, T3B_1`; `I₄₁, J₄₁ ↦ T3C-Ḡ_0, T3C-Ḡ_1`; `I₄₂, J₄₂ ↦ T3C-tr_0, T3C-tr_1`. `MM`, `MǦ`, `ǦM`, `T2a`, `T2b` have no literal band counterpart (they come from `G = Ǧ + M` and from the single-edge `lanlw`) and stand in for `I₁`, `J₁`. No band term is dropped.

**1.3 Kernels.** `(W − 1)` and `S⁺ = SW` are offset-independent: `(W−1)_{xβ} = W^{-d}𝒦̃_{[x][β]}`, `𝒦̃ := (1 − tM⁺_B)⁻¹ − 1`, `M⁺_B := M^{(B)} ∘ M^{(B)}` (`d402.py`: block form to 1.8e-14). So `Σ_{α∈[a₁]} W_{αw} = ω_{a₁}([w])`, `ω := (1 − tM⁺_B)⁻¹`, replaces the band's `K = S^{(B)}(m + m³K⁺)` (`LWExpTerm4.lean:19`).
Numbers at `g = 1/64, 1, 10`, `t = 1/2` (`kern.py`): `ρ(tM⁺_B) = 0.4996, 0.4469, 0.4994`; `max_a Σ_c|ω_{ac}| = 0.667, 0.976, 0.990`.

**1.4 The supervisor's example.** The `I₁` analogue with `Σ_β M_{xβ}M_{βy}` (`MM`, `T1`) is **never** turned into a `𝓛^{(2)}`. Two `M` edges put `x, β, y` in one atom (`M_{xy} = 1[offsets equal] M^{(B)}_{[x][y]}`, `BAMfine_eq`, `BA/GreenSchur.lean:93`), the sum over `x ∈ [a], y ∈ [b]` has `W^d` terms, and `ba_xy_count` (probe 184) gives the extra `W^{-d} ≤ (g²+1)Ψ²`. The band's `𝓛^{(2)}` is replaced by the *twisted* 2-loop of §2 when exactly one `M` edge remains.

## 2. W2: the generic interface does not fit

- The band pins are loop statements with kernels. `LWExpI1K` (`:81`) is `Σ_{a₁} K_{a₁b} 𝔼[(𝓛^{(1)}_{a₁} − m) 𝓛^{(2)}_{(a,b)}]`; `LWExpI23K` (`:96`) and `LWExpI41K` (`:115`) are products of `Lloop` over *independent* block labels (`LWExpTerm2.lean:81-127`; proofs `LWExpTerm4.lean:903, 1316, 1618`).
- The carrier has `L, K, G, M, S, eta, m` (`Chain/Carrier.lean:55-71`) and the loop `tr(Π G(σ_i) E_{a_i})` (`loopM`, `Loop/GLoopFlow.lean:92`): consecutive entries share one vertex.
- At BA the tie `M_{wγ} = 1[offsets equal] M^{(B)}_{[w][γ]}` joins vertices of **different blocks** at one offset. `Σ_{x∈[a]}Σ_{w∈[c₁],γ∈[c₂]} Ǧ_{xw}M_{wγ}Ḡ_{xγ} = M^{(B)}_{c₁c₂} Tr(Ǧ_{ac₁}^T Ḡ_{ac₂})`: a loop with an off-diagonal block insertion `P_{c₁c₂}`, the offset-twisted loop `twL2` (probe 219; one-loop `twTr`, probe 213). Compiled: `twTie` (probe 226: for any `G₁, G₂`, if `M_{wγ} = 1[offsets equal] MB_{[w][γ]}` the tie sum is `MB_{c₁c₂}` times the twisted loop, `G₁ = Ǧ`, `G₂ = G`) and `twTie_ba` (probe 256: at `baFMz`, from `BAMfine_eq`). For `c₁ = c₂` it is an `E_a`-loop; for `c₁ ≠ c₂` it is none. `ba_twist_kernel_ne` (probe 298, compiled; `d > 0`, `Im m > 0`, `g₀ ≠ 0`): `M^{(B)}_{0b} ≠ 0` for some `b ≠ 0`.
- **Decision: no.** `LWExpI1K/I23K/I41K` cannot be stated over `FlowFM` so that `T2`, `T3B`, `T3C-Ḡ`, `MǦ`, `ǦM` instantiate them. L4a is a twin (not G: no tripwire); `lwExpTerm4_kerSum` (`LWExpTerm4.lean:100`) is model-free and is reused by import. L4a2 (the reduction `LWE → LWcut`, `≺ → 𝔼`, `lwTermEXP_of_cut`, `LWExpTerm.lean:286`) keeps its 1,068 central lines.
- **BA statements.** (S1) the crude families `{MM, T1, T3A, lanlw-children with two weights}`: `‖Σ_F 𝔼‖ ≺ η^{-1}B^{5/2}` from `LWAvgLaw`, `|𝔼 tr| ≺ B²`, `STLocalEntry`, row sums of `M^{(B)}`, `ω`. (S2) the twisted families `{T2, T3B, T3C-Ḡ}`: the same bound from `BATwistLaw` and `STLK`, `STLmax` for `𝓛^{(2)}`. (S3) the graph families `{T3C-tr}` and the `∂tr` children: `W^{-2d}Σ_{x,y}𝔼 Γ_{μ,xy} ≺ η^{-1}B^{5/2}` from §3 and the leaf bound. Assembly `BALWCutExp ← S1, S2, S3` (`BALWCutExp`, probe 353, instance 373) and `BALWtermEXP ← BALWCutExp`.

## 3. W3: lever C

**3.1 The pointwise claim fails.** The all-`M` leaf of case (1) `α = γ = β` (`baAllM`, probe 40): `S_{αα}S_{αα}M_{xα}M_{αα}M_{αα}M_{αy}M̄_{xy}`, `(n_S, n_W, n_A) = (0, 2, 0)`, `ord = 4`, `x ~ y` (`ba_pointwise_fails`, probe 56). Its size is `W^{-2d}`: `D_xy/(η^{-1}Ψ⁵) = 1.4e-3, 0.46, 105.8` at `W = 27`, `g = 1/64, 1, 10`, growing like `W^{d/2}` ((a) row 5). `g5.py`: of the 160 normal terms at `x ≠ y`, 28 do not reach `ord ≥ 5` by `GG` in depth 3, all with `x ~ y` (`ord` 4: 21, 3: 6, 2: 1); under the target of 3.2 none fails.

**3.2 Corrected claim.** `ord(Γ_{μ,xy}) ≥ 5 − 2·1[x ~_Γ y]` (`~` = same atom).
Reason: atom-mates have one offset, so the pairs `x ∈ [a], y ∈ [b], x ~ y` number `W^d`, and `W^{-2d} W^d η^{-1}Ψ^{ord} ≤ (g²+1) η^{-1}Ψ^{ord+2} ≤ (g²+1) η^{-1}Ψ⁵` for `ord ≥ 3` (`ba_xy_count`, from `STBctl_ge`, `Induction/ScaleFacts.lean:126`, model-free).
`x = y` is the case `x ~ x`: the count the paper omits (`B:68-77`, (a) row 7) is the same step.

**3.3 Lemma (GG with context).** `Γ` normal, `v` internal with `Ǧ_{y'v}Ǧ_{vy}` of one charge. (H1) `atom(v)` is internal and meets exactly these two solid edges; (H2) `atom(v), atom(y'), atom(y)` are pairwise distinct; (H3) `atom(y')` or `atom(y)` is internal. Then every term of `GGGamma` (after `G = Ǧ + M`) has `ord ≥ ord Γ + 1`. Counters `(Δn_S, Δn_W, Δn_A) → Δord` (`family.py` on the compiled parent `baCtx`; the ranges by `lemma_final.py`):

| term | `(Δn_S, Δn_W, Δn_A)` | `Δord` |
|---|---|---|
| `T1` | `(−2, 1, −1)` (`β` merges two atoms) | 2 |
| `T2a`, `T2b` | `(−1, 1, 0)` | 1 |
| `T3A_k`, `Ǧ` / `M` split of `G_{γy}` | `(1, 1+k, 1+k)` / `(0, 1+k, k)` | 1 / 2 |
| `T3B_k`, 0 / 1 / 2 `M` edges | `(1, 1+k, 1+k)` / `(0, 1+k, k)` / `(−1, 1+k, k−1)` | 1 / 2 / 3 |
| `T3C_k` | by the number of `M` splits | 1 … 4 |

`lemma_final.py`: 14,331 random parents satisfying H1-H3 give exactly these ranges. **Without H2, H3 the paper's `(eq:GGraisesord)` (`B:99`) is false at BA:** `T1` has `Δ = 0` (merged `baGGT1_ord`, `baGGLhs_ord`, `BAVocab.lean:1241, 1249`: `y, y'` external); among 19,414 random pair-only parents 9,491 `T1` and 3,875 `T3A` children have `Δ ≤ 0`. Compiled: `baCtx_T1_ord` (`Δ = 2`, probe 71), `baCtx_families_ord` (`T2a` +1, `T3A` +1, probe 112).

**3.4 Closure** (`tree5.py`, `parents.py`): cases (1)-(4) and `α = β ≠ γ` (`B:102-108`), each at `x ≠ y` and `x = y`, 32 normal terms each: 320 terms, 311 are leaves at once, **9** are expanded.

| case | `ord / target` | `(n_S,n_W,n_A)` | `M` edges | `GG` at | children | below target | leaves |
|---|---|---|---|---|---|---|---|
| `x≠y`, (2) and (3) | 4 / 5 | `(4,2,2)` | 1 | `α` | 47 | 0 | 47 each |
| `x≠y`, (4) | 3 / 5 | `(5,2,3)` | 0 | `α` | 63 | 14 (margin −1) | 1,027 |
| `x≠y`, (4) | 2 / 3 | `(4,2,3)` | 1 | `α` | 47 | 0 | 47 |
| `x≠y`, (4) | 4 / 5 | `(4,2,2)` | 1 | `α` (×2), `β` (×2) | 47 | 0 | 47 each |
| `x=y`, (4) | 2 / 3 | `(4,2,3)` | 1 | `α` | 47 | 0 | 47 |

The 14 below-target children are each closed by one more `GG`. Leaves: 1,403 for the 9, 1,714 in all; depth ≤ 2; minimal margin to the target 0. Leaf properties `n_M ≤ 1`, `n_W ≥ 2`, every internal molecule attached to ≥ 2 solid edges: 0 violations in 1,714 (`int_mol_ok`). Strategy `S*`: `GG` at a vertex with `atom(y') ≠ atom(y)` (all 9 parents have one). This is the paper's case analysis with the target corrected.

**3.5 Decision: C.** A paper-level proof (3.2-3.4; constants `g² + 1`, `t^{n_W} ≤ 1`, 1,714 leaves, a fixed number). In Lean the Lemma's counters belong to L2c2 (as `lanlw_ord`, `BAExpandWOrd.lean:781`, T2315); L4e-C proves the leaf half (the 9-parent table and the properties); **no** `cert_all'`, `belowOf'`, `partitionSim`, `Sound` twins and no 31-93 min merge. Compiled: `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand` (probe 158-166), non-vacuity (probe 169-179).

## 4. W4: the identity in expectation (row 15 of T2325)

- Statements (probe 135-153): `baG5Graph k s : BAGraph (Fin 2) (Fin 3)` (twin of `LWG5Graph`, `LWExpTerm3.lean:54`) and `BAG5Identity d Ls`: for all `L, W, g₀, E, t, m` with `BASelf`, `0 ≤ t < 1`, `k, s, x, y`, `𝔼 (baG5Graph k s).val = Σ_{q ∈ Ls k s} 𝔼 q.val` at `BAlwData` (`BAExpandW.lean:98`, law `PF d L W 0`). No exponent pairs: the band's `m^j m̄^{j'}` are `M`-dotted edges, `(1 + M⁺S⁺)` is the `S⁺`-waved chain.
- The engine `expandG_sum` (`LWExpTerm5.lean:234`, any carrier, weight `w = fun _ => 1`) is reused by import; instance at `BAPGraph (Fin 2)` compiled (probe 393-395). The step is `GG` at `(v, i₁, i₂)` (a vertex and two same-charge edges; name `BARCand` proposed, not the band's blue uncircled `LWG5Cand`, `:65`); its identity is `BAGGGamma` (owed by L2c2) with the D402 coefficient; the root is `BAGraph.partition` (`BAVocab.lean:229`).
- `LWG5Progress` (`:72`) does **not** hold at BA in general: `baTwB_stuck` (probe 97) has `ord 3`, no `GG` candidate, `x ≁ y`. It holds for the `𝒢_xy` tree under `S*` (3.4).
- **D402 checked in expectation** (`mc_gg.py`: `d = 1, L = 3, W^d = 2, t = 1, g = 0.7, z = 0.2 + 0.5i`, GUE blocks, 10⁶ samples, indices at one offset). `f = 1`: `𝔼 LHS = −0.00135+0.00871i`, corrected RHS `−0.00142+0.00872i`, printed RHS `0.04323−0.02006i`. `f = Ḡ_{xy}`: `0.00050+0.00843i`, `0.00046+0.00844i`, `0.01813+0.00323i`. Corrected within `6.8e-5` and `4.6e-5` (Monte Carlo error `1.0e-4`, `4.2e-5`); printed off by `5.3e-2`, `1.8e-2`. The algebra `W − 1 = M⁺SW` is compiled (`ba_W_sub_one`, probe 119).

## 5. W5: pins of the rows (T2184 precedent)

| row | pin | status |
|---|---|---|
| L4d | `BAG5Identity d Ls` (probe 149); `expandG_sum` by import (instance probe 393-395); the step lemma from `BAGGGamma` | compiled |
| L4e-C | `BAG5Tgt`, `BAG5Leaf`, `BAG5Expand` (probe 158-166); instance (probe 169-179) | compiled |
| L4c | leaf bound `Γ_{μ,xy} ≺ t^{n_W} η^{-1}(W^{-d}B_{t,0})^{ord/2}` for normal packed graphs: joined (`n_M = 0`, pathwise, `lwExpTerm6_pathwise`, `LWExpTerm6.lean:76`): `BAGraphPrecJoin` (probe 357; instance 380), from `STLocalEntrygL` alone; `q = 1`, attached ≥ 2 (`(eq:Gbyxi2_BA)`, `B:428`): text with the stage-G pins; plus `ba_xy_count` | joined compiled; `q = 1` text (L3c1, L3c3, L3d1) |
| L4a, L4a2, L4b | `BALWCutExp` (probe 353; `LWCutExp_iff` at the band is `Iff.rfl`, probe 349; instance probe 373); the families S1-S3 of §2 | cut pin compiled; families text |
| §8 | `BATwistLaw` (probe 281) | compiled `Prop`, **no producer** |

Hypotheses that stay: stage G `BAGbEXPij'`, `BAGbEXPii`, `BAGbEXPav` (`(initialGT2)`); K12 `STKwardgL`; Step 1/2 `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL` (`Chain/Carrier.lean:80-121`, `Chain/LWGen.lean:48`).

## 6. C1/L5: constants at `g = 1/64, 1, 10`, `κ := Im m / 2`

| quantity | `g = 1/64` | `g = 1` | `g = 10` | source |
|---|---|---|---|---|
| `Im m` | 0.9993 | 0.6860 | 0.6669 | (a) row 8 |
| count constant `g² + 1 = c_g⁻¹` (`ba_xy_count`) | 1.0002 | 2 | 101 | `STBctl_ge`; `B_{t,0}/c_g` at `t = 1/2`: 2.07, 1.48, 8.49 ((a) row 6) |
| `ρ(tM⁺_B)` | 0.4996 | 0.4469 | 0.4994 | `kern.py` |
| `max_a Σ_c |ω_{ac}|` | 0.667 | 0.976 | 0.990 | `kern.py` |
| twisted / diagonal: `Σ_{c₁≠c₂}|M_{c₁c₂}||𝒦̃|` against `Σ_c |m| 𝒦` | 0.003 | 4.255 | 3.905 | `twist.py` |
| crude / target for `T3C-Ḡ` (`B^{-1/2}`) at `W = 27` | 97.4 | 163.0 | 484.0 | `crude.py` (`W = 10⁴`: 6.9e5, 1.2e6, 3.4e6) |

Nothing in §3 uses smallness of `g` or of `M − m₀I`; the twisted terms of §8 are small only at `g = 1/64`. Uniform BA facts used: `BAMfine_eq`, `BAMfine_decay` (`BA/GreenSchur.lean:124`), `BAMB_row_l1` (`:139`), `BAReal` (`BA/MFixedPoint.lean:432`).

## 7. Row table (L4 after W2 and W3; central lines; ratios of T2387 §6: TW 0.73 / 0.85 / 1.61, NW 0.85 / 1.20 / 2.10)

| row | content | basis | cl | lo / central / hi | role | lane |
|---|---|---|---|---|---|---|
| L4a | BA families S1, kernels `ω`, tie sums, fine-level Ward (twin) | `LWExpTerm4` 1-1838 | TW | 1,342 / 1,562 / 2,959 | h | |
| L4a2 | reduction `LWE → LWcut`, `≺ → 𝔼`, assembly of S1-S3 | `LWExpTerm` 1-1256 | TW | 917 / 1,068 / 2,022 | h | |
| L4b1 | `GGGamma` at `α` for `f = tr Ḡ_{xy}`: families, `W − 1` block form | `LWExpTerm2` first half | NW | 900 / 1,270 / 2,220 | m | |
| L4b2 | families S2 (needs §8) and block evaluation | `LWExpTerm2` second half | NW | 899 / 1,269 / 2,224 | m | |
| L4c1 | bridge to `𝒢_xy`, assembly, `x ~ y` count | `LWExpTerm3` part | NW | 782 / 1,104 / 1,933 | m | |
| L4c2 | leaf bound `q ≤ 1`, joined (atoms) | `LWExpTerm3` part | NW | 1,174 / 1,657 / 2,899 | m | |
| L4d | BA identity half | `LWExpTerm5` -(189-250) | TW | 494 / 575 / 1,090 | h | |
| L4e-C | leaf half: the 9-parent table and the properties (the Lemma is in L2c2) | new | F | 800 / 1,200 / 2,200 | m | none |
| L4g | joined-graph pathwise bound, consumer, Step 6 closures | `LWExpTerm6` | NW | 641 / 905 / 1,583 | m | |

Totals 7,949 / **10,610** / 19,130 (T2387: 10,036 / 13,513 / 23,699; 12,138 with the planning ratio 1.144). Dropped: L4e1, L4e2, L4f1, L4f2 (4,854 central). Stage L: 32 rows, flag 48. L4b and L4c are split (each was above 1,500); L4f2 is gone. The lane has no heavy certificate merge. Not priced: the input of §8.
Order: L4d, L4e-C, L4c and the reduction of L4a2 need only §3 and the L3 outputs; L4a, L4b and the assembly of L4a2 wait for the answer to §8.

## 8. The missing step, the question to Jun, deltas, limits

**Missing step (one).** Family `T3C-Ḡ`: the derivative of `Ḡ_{xy}` in the third sum of `GGGamma` (band `I₄₁`, `(eq:termI41)`, `B:58-64`). After `Σ_{α∈[a₁]}`, up to the factor `t`,
`𝒰 = W^d Σ_{a₁,c₁,c₂} ω_{a₁}(c₁) M^{(B)}_{c₁c₂} 𝔼[ tr(ǦE_{a₁}) · 𝓛̃_{(a;c₁,c₂)} · 𝓛^{(2)}_{(−,+),(c₂,b)} ]`, `𝓛̃ = twL2` (probe 219). Needed: `|𝒰| ≺ η^{-1}B^{5/2}`. Evidence:
1. Entrywise and Ward bounds give `η^{-1}B²`, short by `B^{-1/2} = 97 … 3.4e6` (§6). The gain is the expectation of `tr` against the deterministic part of `𝓛̃` (`𝔼 tr ≺ B²`), which needs `|𝓛̃ − 𝒦̃| ≺ B^{3/2}`.
2. `lem:main_ind_BA` and the pins (`STLKgL`, `STLmaxgL`, `LWAvgLawgL`) control `E_a`-loops only; at `c₁ = c₂` the bound is the band's.
3. The deterministic part of `𝓛̃` is not small at `g ≍ 1` (§6).
4. The pure graph route stalls: `elw_summary.py` with weights, `lanlw` at any tail or head, and `GG` (depth 5): the three `x ≁ y` root terms never reach the target. The stuck graphs of `eng.py` (`regen.py`, `elw.py`) are 4-cycles whose `M`-ties separate the two edges at an atom (no vertex carries both: `baTwB_stuck`, probe 97).
5. One `lanlw` on `Ǧ_{xα}` (tail `x`) of the stuck graph (34 children, 3 with `Δord = 0`): the derivative on `Ḡ_{xγ}` with both new edges circled regenerates `Ǧ_{να}Ǧ*_{νγ}` with `α ~ γ` at `Δord = 0` and no `GG` candidate.
Two closing forms: (R1) a local law for loops with an off-diagonal block insertion, lengths 1 and 2 (`BATwistLaw`, probe 281); (R2) an expansion identity for `Ǧ_{y'u}M_{uv}Ǧ_{vy}` at an atom. The families `T2`, `T3B`, `MǦ`, `ǦM` are twisted at first level, but one more `lanlw` gives two weights (not verified): they may need no input.

**Question to Jun (one).** In the BA proof of `lem:LWterm_EXP` (`B:118`: "analogous … `GGGamma` in place of `(Oe2x)`"), the derivative of `Ḡ_{xy}` in `GGGamma` produces `Ǧ_{xw}M_{wγ}Ḡ_{xγ}|G_{δy}|²` with `M_{wγ}` joining different blocks (the band's `I₄₁` has `mδ_{wγ}`), and `lem:main_ind_BA` controls `E_a`-loops only. How do [yang2024Del, App. B] or [RBSO1D] bound `𝔼[tr(ǦE_{a₁}) Ǧ_{xw}M_{wγ}Ḡ_{xγ} 𝓛^{(2)}]`: (R1) by a law for loops with an off-diagonal block insertion (statement?), or (R2) by an expansion of `ǦMǦ` at an atom (identity?)?

**Paper-delta candidates.**
- `T2398a`: `(eq:sizeGammamu_E)` is false pointwise at BA; corrected target `5 − 2·1[x ~ y]` (3.1-3.2).
- `T2398b`: `(eq:GGraisesord)` needs H1-H3 (3.3; extends `T2387b`).
- `T2398c`: the atomic correspondence (`B:320-323`) fails for the rules: `GG` needs both edges at one vertex (`baTwB_stuck`).
- `T2398d`: `B:118` omits the twisted loops (§8).
- `T2398e`: `S^{(B)} = I` (`B:289`): `a₂ = a₁`, kernel `ω`, not `K`.
- `T2398f`: D402 checked in expectation (§4; evidence for `T2161a`, `T2387a`).

**Limits.**
1. The engine models counters, atoms and molecules, not values. Its rules are `B:361-405` as printed; the transposed `lanlw` is derived by hand here (not in the paper, not checked numerically); "stuck" means within these rules and depth 5.
2. The closure and the Lemma are exhaustive on the 320 terms and randomized (14,331 parents) beyond; the Lean proof of the Lemma is owed by L2c2.
3. `Kt` in `BATwistLaw` is the expected ladder, not derived.
4. The Monte Carlo is at `W^d = 2`, `L = 3`: an exact identity, not an asymptotic statement.
5. Rows are extrapolations by T2387's ratios; L4e-C and the splits are estimates; the twisted-law input is unpriced.
6. The leaf bound `(Gammamuxy)` and the properties beyond `n_M`, `n_W`, attachment (`LWAttached`, `LWJoined`) belong to L4c.

## (b′) Amend 2 (route R1): the TL1/TL2 pins, the rows under R1, T2398d — Sun Oct 11 08:24:56 UTC 2026 (`date -u`)

Prover `claude-sonnet-5-5` (prover-max, design update). Inputs: `docs/tickets/T2398-amend-2.md` (binding), `docs/supervisor/2026-10-11-0652.md` (Q1-Q4, C1-C4), `docs/tickets/T2398-analysis-fable.md` §2-§6, `docs/tickets/T2398-TL-proofs.md` (A.2, T.1-T.3, T.7, T.12). Probe `RBM3D/Probe/T2398Pins.lean`: 498 lines (limit 500), commits `4c2955a`, `e46a4d6`, `641c9d4`, `6429bb5` on `2257f54`. §0-§8 are unchanged (line 3 there, 399 lines and the last edit at 00:08:18 UTC, is the round-1 record). `probe N` below is a line of the probe at `6429bb5`; lines 1-275 keep their round-1 numbers (the citations of §0-§8 to them stay valid), the later citations of §0-§8 are lines of `2257f54`. Build, exit code, axioms, clash grep, diff stat and the instances: `docs/reports/T2398-prove.md` (b), round 2. Scripts (scratchpad `T2398/`, not in the repository): `extract.py`, `cmp_cut.py`, `conv.py`, `limit2.py`, `basis2.py`, `rows.py`. The STOP in line 1 is resolved by Amend 2: TL1 and TL2 enter the BA chain as owed text pins with the standing of `STLKgL` (0652 Q3); their producers are a new BA stage (0652 C4), not priced here.

| item | result |
|---|---|
| D2 | `BATwistLaw` is replaced by `BATwistAvgLaw` (probe 323, TL1), `twK` (306), `BATwistLoopLaw` (328, TL2: uncircled `twL2'` 298, exponent 3/2, all `σ ∈ {±}²` and `(a, c₁, c₂)`, per `τ`, no `∃ Kt`); statements `twFold` (340), `twWard` (345), `twK_bound` (360), `twCirc` (352); the index convention (276-278); `twL2_eq`, `twTr_eq` (`rfl`), `twMB_ba` (311); the cut pin with seven premises `BALWCutExpTw` (434), instances (467, 474) |
| D3 | §C: L4b2 TW 916 / 1,067 / 2,021 (basis 1,255); L4a2 unchanged, seven premises; new row L4t (F, role h) 320 / 450 / 700; central 10,858; no row waits for §8 |
| D4 | T2398d recorded in the supervisor's wording (§D) |

### A. The statements of D2 (extracted by script, `python3 SP/extract.py <names>`; probe line first)
```
323: def BATwistAvgLaw (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ‖twTr C n (τ n) ω p.1 p.2‖)
    (fun n _ _ => sz.Bctl n (τ n))
306: def twK (n : ℕ) (t : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a' : Zd d (sz.L n), PropThetaQ (BAMss d (sz.L n) (twMB C n) (σ 0) (σ 1)) t a a' *
    BAMsigma d (sz.L n) (twMB C n) (σ 0) c₂ a' * BAMsigma d (sz.L n) (twMB C n) (σ 1) a' c₁
298: def twL2' (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  twLoopX n (twChg (C.G n t ω) (σ 0)) (twChg (C.G n t ω) (σ 1)) a c₁ c₂
288: def twLoopX (n : ℕ) (X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (a c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, X₂ x w * X₁ (twShift n c₂ w) x
284: def twTrP (n : ℕ) (X : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (c₁ c₂ : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ w ∈ twBlk n c₂, X w (twShift n c₁ w)
328: def BATwistLoopLaw (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => ‖twL2' C n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK C n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
    (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ))
340: def twFold (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (X₁ X₂ : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (a c₁ c₂ : Zd d (sz.L n)),
    ‖twLoopX n X₁ X₂ a c₁ c₂‖ ^ 2 ≤ twSq n X₁ c₂ a * twSq n X₂ a c₁
345: def twWard (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (G : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (η : ℝ), η ≠ 0 →
    G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G * G.conjTranspose) → G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G) →
    ∀ (σ : Bool) (c₁ c₂ : Zd d (sz.L n)), ∑ a, twLoopX n (twChg G σ) (twChg G (!σ)) a c₁ c₂ =
      (2 * Complex.I * (((sz.W n : ℕ) : ℂ) ^ d) * (η : ℂ))⁻¹ * (twTrP n (twChg G true) c₁ c₂ - twTrP n (twChg G false) c₁ c₂)
352: def twCirc (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (X₁ X₂ M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ),
    (∀ w γ, M w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
      MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0) →
    ∀ a c₁ c₂ : Zd d (sz.L n), twLoopX n X₁ (fun x y => X₂ x y - M x y) a c₁ c₂ =
      twLoopX n X₁ X₂ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB a c₁ * twTrP n X₁ a c₂
360: def twK_bound (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ (n : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
        (∀ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ C * sz.Bctl n (t n)) ∧
        ∑ a, ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ C * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹
$ python3 SP/cmp_cut.py      # `BALWCutExpTw` (434) against `LWCutExpG` (413)
conclusions identical (modulo (law sz) = μ, (mk sz z) = baFMz sz z): True
premises of BALWCutExpTw = premises of LWCutExpG + TL1, TL2: True
```
- Convention (probe 276-278, the proofs'): `Tr(X P_{c₁c₂}) = W^{-d} Σ_o X_{(c₂,o),(c₁,o)}` (`twTrP`), `G(−) = G^*` (`twChg`), `L̃_{σ,(a;c₁,c₂)} = Tr(G(σ₁)E_aG(σ₂)P_{c₁c₂})` (`twLoopX`, `twL2'`). The probe's `twL2` is `L̃_{(−,+)}` with the leg at `c₁` circled and `twTr c₁ c₂` is `T̃_{+,(c₂,c₁)}`, both by `rfl` (`twL2_eq`, `twTr_eq`); TL1 over all ordered pairs is unaffected and one charge suffices (`T̃_−(c₁,c₂) = conj T̃_+(c₂,c₁)`, 0652 C3).
- `twK`: `FlowFM` has no `Θ` field. `Θ^{(σ₁σ₂)}_t = (1 − tM^{(σ₁σ₂)})⁻¹` is `PropThetaQ` (`Propagator/Pins.lean:214`) of `BAMss` (`BA/MFixedPoint.lean:511`; `M^{(σ₁σ₂)}_{ab} = M(σ₁)_{ba}M(σ₂)_{ab}`, `|M^{(B)}_{ab}|²` for `(−,+)`, not `M∘M`) of the block matrix `twMB` read off the carrier's `M`; at `baFMz` it is `BAMB` (`twMB_ba`, from `BAMfine_eq`, `BA/GreenSchur.lean:93`), so `twK` is built from `BATheta` (`BA/MFixedPoint.lean:515`).
- `BALWCutExpTw` has the conclusion and five premises of `LWCutExpG` and TL1, TL2 as two more (script above); `BALWCutExp` (431, five premises) stays as the statement of round 1.

### B. Numeric checks of the convention and of the exponents (d = 1, `False` = charge −; `conv.py` mirrors the Lean definitions)
```
$ python3 SP/conv.py
resolvent identities G-G* = 2i eta G G* = 2i eta G* G, max err: 7.9e-16 1.1e-15
twWard  max |lhs - rhs| over sigma, c1, c2: 6.9e-17
twCirc  max |lhs - rhs|: 3.3e-16
twFold  max |L|^2 / (sq sq) (must be <= 1): 0.166
base case: twLoopX of M(s1), M(s2) = W^-1 M(s1)_{c2 a} M(s2)_{a c1} = K~ at t = 0, all 4 charges: max err 2.2e-16
twTr_eq: err 0.0e+00;  T_-(c1,c2) = conj T_+(c2,c1): err 0.0e+00
Monte Carlo E L~ vs K~ (static z = i eta, d = 1, L = 4, W = 12, g = 1, eta = 0.3, 1500 samples; a = 0, c1 = 1, c2 = 2):
  sigma=(False, True): E L~ = 4.196e-05+8.258e-03j  K~ = 0.000e+00+8.214e-03j  |E L~ - K~| = 6.0e-05  MC err 7.4e-05  |E L~ - K~(c1<->c2)| = 1.6e-02
  sigma=(True, True): E L~ = 1.112e-05-6.442e-03j  K~ = 0.000e+00-6.531e-03j  |E L~ - K~| = 9.0e-05  MC err 8.5e-05  |E L~ - K~(c1<->c2)| = 9.0e-05
  sigma=(True, False): E L~ = 4.468e-05-8.294e-03j  K~ = 0.000e+00-8.214e-03j  |E L~ - K~| = 9.1e-05  MC err 7.4e-05  |E L~ - K~(c1<->c2)| = 1.7e-02
  sigma=(False, False): E L~ = 7.576e-05+6.602e-03j  K~ = 0.000e+00+6.531e-03j  |E L~ - K~| = 1.0e-04  MC err 8.5e-05  |E L~ - K~(c1<->c2)| = 1.0e-04
$ python3 SP/limit2.py
W    sd|T~|*W   rms|L~-K~|*W^2   rms|L~-K~|*W^{3/2}   (d = 1, B_{t,0} := 1; sigma = (-,+); a = 0, c1 = 1, c2 = 2)
  6    0.4461        0.4318            0.1763
 12    0.4621        0.4218            0.1218
 24    0.4689        0.4295            0.0877
```
Reading: `twWard`, `twCirc` and the base case `L̃_0 = K̃_0` (`G_0 = M`, `t = 0`, `twK` at `t = 0`) hold at random data to 1e-16, `twFold` with the ratio 0.17 ≤ 1; `E L̃` equals `twK` for the four charges within about one Monte Carlo error, and for `(−,+)`, `(+,−)` not with `c₁ ↔ c₂` swapped (1.6e-2): the sign fixes the convention. `sd T̃ · W` and `rms(L̃ − K̃) · W²` are constant in `W`: `|T̃| ≍ W^{-d}` (TL1 has no slack) and `|L̃ − K̃| ≍ W^{-2d}`, so TL2 at exponent 3/2 has the slack `W^{-d/2}` (last column).

### C. Row table (design §7 under R1; central lines; ratios of T2387 §6: TW 0.73 / 0.85 / 1.61, NW 0.85 / 1.20 / 2.10, F by estimate; role h = `prover-hard`, m = `prover-max`)
| row | content | basis | cl | lo / central / hi | role | change |
|---|---|---|---|---|---|---|
| L4a | BA families S1, kernels `ω`, tie sums, fine-level Ward (twin) | `LWExpTerm4` 1-1838 | TW | 1,342 / 1,562 / 2,959 | h | none; waits for L0 and the K12 pins only |
| L4a2 | reduction `LWE → LWcut`, `≺ → 𝔼`; assembly of S1-S3 with TL1, TL2 as hypotheses (`BALWCutExpTw`, 434) | `LWExpTerm` 1-1256 | TW | 917 / 1,068 / 2,022 | h | two more premises; price unchanged |
| L4b1 | `GGGamma` at `α` for `f = tr Ḡ_{xy}`: families, `W − 1` block form | `LWExpTerm2` first half | NW | 900 / 1,270 / 2,220 | m | none |
| L4b2 | twisted twin of `lwExpI1K_holds` (`MǦ`, `ǦM`, `T2`), `lwExpI23K_holds` (`T3B`: TL1 for `Tr(G̊E_{a₂})`) and `lwExpI41K_holds` (`T3C-Ḡ`) with `(twL2', twK, twTr)` for `(𝓛^{(2)}, 𝒦^{(2)}, Tr(G̊E))`; hypotheses `BATwistAvgLaw`, `BATwistLoopLaw` | `LWExpTerm4` 828-1716 (889) + 14 helpers (366) = 1,255 | TW | 916 / 1,067 / 2,021 | h | was NW 899 / 1,269 / 2,224 (m) |
| L4c1 | bridge to `𝒢_{xy}`, assembly, `x ~ y` count | `LWExpTerm3` part | NW | 782 / 1,104 / 1,933 | m | none |
| L4c2 | leaf bound `q ≤ 1`, joined (atoms) | `LWExpTerm3` part | NW | 1,174 / 1,657 / 2,899 | m | none |
| L4d | BA identity half | `LWExpTerm5` -(189-250) | TW | 494 / 575 / 1,090 | h | none |
| L4e-C | leaf half: the 9-parent table and the properties | new | F | 800 / 1,200 / 2,200 | m | none |
| L4g | joined-graph pathwise bound, consumer, Step 6 closures | `LWExpTerm6` | NW | 641 / 905 / 1,583 | m | none |
| **L4t** | model-free `twFold`, `twWard`, `twCirc`, `twK_bound` (probe 336-365) | statement level (analysis §6: `twFold` ~150, `twWard` ~100, `twK_bound` ~200; `twCirc` inside the margin, its core `twTie` is 27 lines, probe 226) | F | 320 / 450 / 700 | h | new |

Totals 8,286 / **10,858** / 19,627 (round 1: 7,949 / 10,610 / 19,130; `rows.py`); 12,422 with the planning ratio 1.144. Stage L: 33 rows (32 + L4t), flag 1.5 × 33 = 49.5, i.e. 50; no row in the certificate lane. L4b2 basis (`basis2.py`): the sections of `lwExpI1K_holds` 112 lines, kernel sums 164, `lwExpI23K_holds` 290, `lwExpI41K_holds` 323 (889), and the 14 declarations they use directly (366); the analysis' 700 / 1,000 / 1,800 are 24% / 6% / 11% below. Overlap: L4a's basis (all of `LWExpTerm4`) holds the same I1K and I41K text; if the L4a ticket leaves it out (435 basis lines) its central falls by 370; not applied (the amend leaves L4a).
Order: L4t needs merged BA files only and can start at once. L4d, L4e-C, L4c and the reduction of L4a2 need only §3 and the L3 outputs; L4a needs L0 and the K12 pins; L4b1 needs L2c2 and L4a; L4b2 needs L4t and the two pins as hypotheses (no producer); the assembly of L4a2 needs L4a, L4b1, L4b2, L4c, L4d, L4e-C. No row waits for §8. Not priced: the producers of TL1 and TL2 (a new BA stage, 0652 C4). Until they exist the terminal BA statement is conditional on two text pins: the merged `BALWtermEXP` (`BA/LWPinsBA.lean:49`) has five premises and its BA proof uses TL1, TL2 under R1, so BA-L6 pins a seven-premise successor (a new name; the merged pin is not changed).

### D. Paper delta T2398d (supervisor 0652 Q4, lines 170-177, verbatim; replaces the round-1 text of T2398d in §8)
> B:118 says the BA case of Lemma B.1 (`lem:LWterm_EXP`) is "analogous … we omit the details". The BA GG-expansion (GGGamma, (B.20)) produces the twisted loops Tr(G^*E_aG̊P_{c1c2}) and Tr(G̊P_{c1c2}) with c1 ≠ c2. These are not G-loops of (2.43), and Theorem 8.2 does not control them. Entrywise bounds plus Ward lose (W^{-d}B)^{1/2}.
>
> **Fix.**
> - (TL1): a lemma in §8, a consequence of Steps 2–3.
> - (TL2): a fifth hypothesis and conclusion of Theorem 8.2, with the twisted tree K̃ = W^{-d}Σ_{a'}Θ^{(σ1σ2)}(a,a')M^{(B)}(σ1)_{c2a'}M^{(B)}(σ2)_{a'c1}.
> - With these, the BA proof of (B.1) is the twin of (B.2)–(B.4).
>
> Not in [68] (analysis §1).

No further delta: TL1 (one charge, ordered pairs), TL2 (exponent 3/2, the proofs give 2 − δ) and `twK_bound` (`Bctl` for `B_{t,|a−c₁|}`, no `e^{-c|c₁−c₂|/2}`: weaker than T.1 (i)) are weakenings of the statements of T2398d.

### E. Limits
1. TL1, TL2 are owed text pins: their truth rests on supervisor 0652 (Q1-Q2: PASS) and on `T2398-TL-proofs.md`; §B checks the convention and the exponents at d = 1 only, not constants in d = 3.
2. `twFold`, `twWard`, `twCirc`, `twK_bound` are statements, not proved in the probe (500-line limit). `twK_bound` (ii) is the private `KWardIneq_theta_col_le` (`BA/KWardIneq.lean:265`, to be copied) with the row identity `Σ_b |M^{(B)}_{ab}|² = 1` of `BAPropM` (third conjunct; `baPropM_holds`, `BA/CombesThomas.lean:562`); (i) needs `baProp5mixed_holds` (`BA/Prop5.lean:928`), `baProp5s_holds` (`BA/Prop5Short.lean:667`) and `BAMfine_decay` (`BA/GreenSchur.lean:124`). Non-vacuity of the hypotheses of `twWard` (a real resolvent) and `twCirc` (a block-tied `M`) is numeric (§B), not compiled; `twK_bound` has the compiled instance 474.
3. `twMB` reads `M^{(B)}` at offset 0 of the carrier's `M`; it is identified with `BAMB` at `baFMz` only (`twMB_ba`, which needs `0 < Im m`).
4. Row prices are estimates (basis × T2387's ratios; L4t is the amend's 450); the producers are not priced.
