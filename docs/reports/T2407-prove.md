Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 04:29:44 UTC 2026

Notation: `x = p.1.src = p.1.dst` (the circled blue loop `G̊_{xx}` of the normal `Γ`), `p.2` the other solid edges, `q ∈ lwSplit p.2`; `SP=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2407`. Scripts are Python models of `BAVocab.lean:92-146`, `BAExpandW.lean:122-146`, `LWWeightExp.lean:658-700` (no Lean).

### (i) Exponent table (the targets have no analytic exponent; the thresholds are `t`, `L`, and the counters of `(eq:ordG_BA)`, `B:353`)

| Quantity | Value | Constraint | Slack |
|---|---|---|---|
| `t` | `1/2` | `0 ≤ t < 1` (`baLweight_holds`, `baW_isUnit`, `BAExpandW.lean:354,247`); rows of `M⁺S` have abs-sum `≤ t·Σ_α|M_{xα}|² = t` | `1 − t = 1/2`; Gershgorin max row sum printed `0.5000000000000008 ≤ 0.5` (equality is the Ward identity) |
| `L` | `3` | `3 ≤ L` (`hL`) | 0 |
| `d`, `W` | `3`; `W = 1` (Lean instance), `W = 2` (numeric, non-scalar `M`) | `d` arbitrary (no `3 ≤ d` used), `NeZero W` | none needed |
| `(self_m)` datum `m` | `i` (`g₀=0,E=0`); `−0.13932615+0.72335186 i` (`g₀=1/2,E=3/10`) | `BASelf`: `0 < Im m`, `m = L^{-d} tr (g₀Ψ^{B} − E − m)⁻¹` | residual `|m − F(m)| ≤ 1.1e-16`, `Im m = 0.723` |
| Kernel `W = 1 + M⁺S⁺` | `S⁺ = S W` (`BAlwData.Sp`) | `W − 1 = M⁺(S W)` follows from `W(1−M⁺S) = 1` (`baW_mul`) by `Matrix`-inverse commutation | numeric `‖(W−1) − M⁺S⁺‖ = 5.5e-14` (`W=2`), `2.9e-16` (`W=1`) |
| `ord` shift (all 4 families) | `+1` raw | `lweight_ord`: `ord Δ = ord Γ + 1` | 0 (equality, 20000 random parents, 0 violations) |
| `ordG Δ − ord Γ` family A1 (`T1`, leaf) | min `1` | `≥ 0` (`lweight_scalingOrderG`) | 1 |
| `ordG Δ − ord Γ` family A2 (`lanlwD` itself) | min `0`, 26533 of 40334 terms attain `0` | `≥ 0` | 0 (tight, as `lanlw_scalingOrderG`) |
| `ordG Δ − ord Γ` families B1, B2 | min `1`, `1` | `≥ 0` | 1 |
| Stop line | ticket: estimate 800 / 950 / 1,700, `wc -l RBM3D/Graph/BAWeightOp.lean ≤ 2,000` | binding | — |

**Term list (the answer to the ticket's 1a questions).** `(B.19)` (`B:376-387`) has only the diagonal `G̊_{xx}` on the left; downstream uses only the self-loop form (`docs/reports/T2395-design.md:84-85`: "`lem_lweight` at a self-loop `Ǧ_{xx}`", Step 2 (1); `docs/reports/T2397-design.md:110` item 4: "`lweight` is used for weights, `lanlw` for edges inside an atom"). So **only `G̊_{xx}` is needed; no `G̊_{xy}` form.** The vocabulary has no kernel edge: `WEdge` is `S` or `S⁺` (`LWVocab.lean:89`, `WEdge.val` :120), `BAMEdge` is `M`/`M̄`. `W_{xy} = δ_{xy} + Σ_a M_{xa}M_{ax}S⁺_{ay}` is therefore two families, on two vertex types (as the band's `owxT1,T3` on `Fin 1` and `owxT2,T4` on `Fin 2`, `owx_graph_E` `LWWeightExp.lean:1316`):

| Term | Vertices (`I ⊕ Fin k`) | Solid | Waved | `M`-dotted | Band twin (`LWWeightExp.lean:658-700`) |
|---|---|---|---|---|---|
| A1 `lweightT1A` (`δ_{xy}` part) | `k=2`: `α,β` | `p.2`, `G̊_{ββ}`, `G̊_{αx}` | `S_{αβ}` (black) | `M_{xα}` | `owxT1` |
| A2 (`δ_{xy}` part, `q`) | `k=2` | **exactly `lanlwD Γ p q`** (`G_{βx}` uncircled: `p.1.dst = x`) | same | same | `owxT3` |
| B1 `lweightT1B` (kernel part) | `k=4`: `a,y,α,β` | `p.2`, `G̊_{αy}`, `G̊_{ββ}` | `S⁺_{ay}` (`col=true`), `S_{αβ}` | `M_{xa}, M_{ax}, M_{yα}` | `owxT2` |
| B2 `lweightDB` (kernel part, `q`) | `k=4` | `q.2`, `owxDE β α q.1` (2 edges), `G_{βy}` | same as B1 | same as B1 | `owxT4` |

All coefficients `+coeff Γ`. A1 differs from `lanlwT1 Γ p` only by the circle on `G_{αx}` (`G_{αx} = G̊_{αx} + M_{αx}`; the `M_{αx}` part is the `M⁺S` term moved into the kernel by `(1−M⁺S)W = 1`). Hypotheses of the targets: `3 ≤ L`, `BASelf d L g₀ E m`, `0 ≤ t < 1`, `p ∈ lwSplit Γ.solid`, `p.1 = ⟨true,true,x,x⟩`; ord claims also `Γ.Normal`. Value statement (shape of `owx_graph_E`, sum of the four expectations): `𝔼 Γ.val = 𝔼 A1.val + 𝔼 B1.val + Σ_q 𝔼 A2_q.val + Σ_q 𝔼 B2_q.val` at `BAlwData` over `PF d L W 0`; at `t = 0` both sides vanish as in `lanlw_val` (`Ǧ = 0`, `S = 0`).

**Counters and where the band's `n_W + 1 or 2` changes (ii).** Raw counters `(n_S,n_W,n_A,n_M)` shift: A1, A2 `(+1,+1,+1,0)`; B1, B2 `(+1,+2,+2,0)`; `ord` `+1` in both. The band shifts are `T1,T3: (+1,+1,+1,0)`, `T2,T4: (+1,+2,+2,0)` in `(n_S,n_W,n_V,n_M)` (`owxT1_counters` :741, `owxT2_counters` :752, `owxT4_counters` :790). Nothing changes in `n_S`, `n_W`, `n_M`. What changes: BA adds 2 resp. 4 new vertices but `n_A` rises by only 1 resp. 2 (`α` joins the atom of `x` by `M_{xα}`; `a` joins it by `M_{xa}M_{ax}`; `{y,α}` is one new atom, `{β}` one; `S⁺_{ay}` and `S_{αβ}` are waved, so they join molecules not atoms; every new vertex stays in the molecule of `x`, `n_M` unchanged). A2 is the existing `lanlwD_counters` (`BAExpandWOrd.lean:769`) and `lanlw_ord`. A1 is the circled variant of `lanlwT1` (counters do not depend on circles); A1 is the circled member of `(lanlwT1 Γ p).splitG` when `Γ` is normal, so its `ordG` bound follows from `lanlw_scalingOrderG` (`BAExpandWOrd.lean:803`); script `member.py` (3000 random normal parents): `A1 equals the circled member of (lanlwT1 Gamma p).splitG: 3000 of 3000`. B-family `ordG`: B1 is normal, `ordG = ord Γ + 1`; for B2 each of the three uncircled edges has an endpoint in a new internal atom (`{β}` or `{y,α}`), so `j` splits give `ord − ord Γ = 1 − j + 2κ` with `κ ≥ 1` once `j ≥ 1`, and `j ≤ 3`: `≥ 0` (script min is `1`).

### (ii) One concrete nondegenerate instance

Hypothesis values: `d=3, L=3, t=1/2`; Lean data `W=1, g₀=0, E=0, m=i` (`BASelf` is `baSelf_zero`, `BAExpand.lean:865`: `M^{(B)} = i·1`, `L^{-d} tr = i`); non-scalar data `W=2, g₀=1/2, E=3/10`, `m` solved numerically (in Lean `hSelf` stays a hypothesis of the example, as in `BAExpandWInst`, `BAExpandW.lean:1014`). The only external hypothesis is `BASelf`; no limit is involved, its concrete computation is the fixed-point residual below.

```
$ cd $SP && python3 instance.py 2 0.5 0.3        # d=3 L=3 W=2 g0=1/2 E=3/10 t=1/2 (n=216)
m = (-0.13932615320437688+0.7233518593541259j)  |m - F(m)| = 1.1102230246251565e-16  Im m > 0: True
fine size n = 216  M not a multiple of 1: True
M symmetric (baM_symm): True
max_x |sum_a |M_xa|^2 - 1| (baM_row_sq): 1.3322676295501878e-15
Gershgorin: max row abs-sum of M+S = 0.5000000000000008 <= t = 0.5 : True
||W(1-M+S) - 1|| = 7.112420660341821e-14
||(W - 1) - M+ S+|| (kernel 1 + M+S+ = W) = 5.456130607546405e-14
|R - (A1+A2+B1+B2)| = 1.1325499295668598e-15  |R| = 0.17590142045382354
$ cd $SP && python3 instance.py 1 0 0            # Lean instance W=1 g0=0 E=0, m=i (n=27)
m = 1j  |m - F(m)| = 0.0  Im m > 0: True
fine size n = 27  M not a multiple of 1: False
M symmetric (baM_symm): True
max_x |sum_a |M_xa|^2 - 1| (baM_row_sq): 0.0
Gershgorin: max row abs-sum of M+S = 0.5 <= t = 0.5 : True
||W(1-M+S) - 1|| = 0.0
||(W - 1) - M+ S+|| (kernel 1 + M+S+ = W) = 2.884444029575346e-16
|R - (A1+A2+B1+B2)| = 2.220446049250313e-16  |R| = 1.8932737651096139
```

`R` = `BAlweightR` (`BAExpandW.lean:70-78`) at `x = a`, `f = G̊_{ab}`, `∂_{h_{βα}} G_{ab} = −G_{aβ}G_{αb}`, random complex `G`, against the sum of the four term values of the table (labels of `a,y,α,β` summed): the term list is an algebraic identity with the kernel `W = 1 + M⁺(SW)`. Counter check of the models against compiled Lean values, and the 20000 random normal parents (loops at external and internal `x`, `×`-dotted, `Ψ`-, `M`-dotted, waved edges):

```
$ cd $SP && python3 counters.py
 lanlwT1 baGcxy   (2, 1, 1, 0) Lean (2,1,1,0)
 lanlwT1 baGcxx   (2, 1, 2, 1) Lean (2,1,2,1)
 lanlwD baGGLhs   (3, 1, 2, 1) Lean (3,1,2,1)
 baGGLhs counters (2, 0, 1, 1) Lean (2,0,1,1)
$ cd $SP && python3 randcheck.py
family  terms   counter-delta-wrong  raw-ord!=ord+1  min(ordG-ord(Gamma))  #terms with ordG==ord(Gamma)
A1      20000            0                0              1                    0
A2      40334            0                0              0                26533
B1      20000            0                0              1                    0
B2      40334            0                0              1                    0
$ cd $SP && python3 inst_graphs.py       # instance graphs for the Lean examples (E,I vertex types as in BAExpandWInst)
baGcxx counters (1, 0, 1, 1) ord -1 ordG -1 normal: yes
   A1 counters (2, 1, 2, 1) ord 0 ordG 0  ord-ord(Gamma) = 1
   B1 counters (2, 2, 3, 1) ord 0 ordG 0  ord-ord(Gamma) = 1
baGwx (G°xx G°ex) counters (2, 0, 1, 1) ord 0 ordG 0 normal: yes
   A1 counters (3, 1, 2, 1) ord 1 ordG 1  ord-ord(Gamma) = 1
   A2 counters (3, 1, 2, 1) ord 1 ordG 0  ord-ord(Gamma) = 1
   B1 counters (3, 2, 3, 1) ord 1 ordG 1  ord-ord(Gamma) = 1
   B2 counters (3, 2, 3, 1) ord 1 ordG 1  ord-ord(Gamma) = 1
```

Instance per target (all at the Lean data above, `ℓe` any): (1) `baGcxx` (`Fin 0`, `Fin 1`; `p = (⟨true,true,inr 0,inr 0⟩, [])`: A1, B1, no `q`) and `baGwx` (`E = Fin 1`, `I = Fin 1`, solid `[G̊_{xx}, G̊_{ex}]`, `x = inr 0`, `e = inl 0`, `p = (G̊_{xx}, [G̊_{ex}])`, `q = (G̊_{ex}, [])`: A1, A2, B1, B2). (2) `lweight_val` on both, hypotheses `3 ≤ 3`, `baSelf_zero`, `0 ≤ 1/2 < 1`, `p ∈ lwSplit Γ.solid` all concrete. (3) counters/`lweight_ord`/`lweight_scalingOrderG` on `baGcxx` (`ord Γ = −1`, terms `ord 0`, `ordG 0`) and `baGwx` (`ord Γ = 0`, terms `ord 1`, `ordG 1,0,1,1`; A2 attains `ordG = ord Γ`). (4) no smallness of `g₀`, `‖M − m₀I‖`; only `BASelf`, `baM_row_sq`, `baW_isUnit` (Gershgorin) enter, as the numeric lines above (Ward, Gershgorin, `W(1−M⁺S)=1`).

### Verdicts
- Target 1 (term list as `BAGraph`s): PASS (two vertex types `I ⊕ Fin 2`, `I ⊕ Fin 4`; no kernel edge in the vocabulary, so `1 + M⁺S⁺` is split into `δ_{xy}` and `M_{xa}M_{ax}S⁺_{ay}`).
- Target 2 (`lweight_val`): PASS (hypotheses hold at the instance; the algebraic identity `R = A1+A2+B1+B2` checked to `1e-15`; `baLweight_holds` is stated through `BAlwf`/`BAlwdf` on `PF d L W 0`, the graph terms need the matching with `owxEdgePoly` products, the 1b's work).
- Target 3 (counters, `lweight_ord`, `lweight_scalingOrderG`): PASS (`+1` raw on all four families; `ordG ≥ ord Γ`, tight only for A2).
- Target 4 (C1 / L5, uniform BA facts only): PASS.
- Target 5 (instances): PASS (`baGcxx`, `baGwx` above).
- Target 6 (registry none, pre-check): nothing to prove in 1a.


## (a′) Preflight corrections — Sun Oct 11 04:52:50 UTC 2026

Rule-(B) repair of the 1a against Amend 1 (`docs/tickets/T2407-amend-1.md`, binding) and the five items of `docs/reports/T2407-1a-audit.md`. Section (a) is not edited. `SP` as in (a); scripts `lwverb.py` (verbatim transcription of the probe), `val.py`, `instverb.py`, `gen.py` are new, Python only, no Lean. Superseded by this section: the names `lweightT1A/T1B/DB`, `lweight_val`, `lweight_ord`, `lweight_scalingOrderG` and the four-expectation value form of (a); the numerics of (a) are unchanged. One correction of (a): "A1 equals the circled member of `(lanlwT1 Γ p).splitG`" holds only up to the order of the solid list (item 1).

### 1. D1: the term lists are the probe's, verbatim (item 1)

Source: `git -C /Users/junyin/Lean_proof/RBM3D show 4c1de4c:RBM3D/Probe/T2395Pins.lean`. The 1b copies, unchanged, into `RBM3D/Graph/BAWeightOp.lean` (namespace `RBM.Graph`): `BAGraph.ext`, `bpv`, `bpS`, `bpM`, `bpW`, `BAGraph.lw2`, `BAGraph.lw4` (lines 105-128, docstring of `ext` included) and `baSum` (239-241). The probe has no `gg2/gg4` in this file (L2c2). Verbatim check for the audit: `sed -n 105,128p | shasum` = `6589d94b2605` (24 lines), `sed -n 239,241p | shasum` = `4506a4b8dd88` (3 lines). No definition was found wrong: `val.py` below checks `lem_lweight` numerically on exactly these lists. Dependencies on `main` (grep by the auditor, §3 of the 1a-audit): `LGraph.owxExt`, `owxEmb`, `owxDE`, `BAPsiEdge.map`, `BAMEdge.map`, `BAGraph.lanlwD`, `lwSplit`.

| (a) family | probe object | relation (script `lwverb.py struct 20000`) |
|---|---|---|
| A1 | head of `Γ.lw2 p` | same graph, solid list order `[Ǧ_{αx}, Ǧ_{ββ}]` vs `[Ǧ_{ββ}, ·_{αx}]` of `lanlwT1` (`BAExpandW.lean:124-125`); `BAGraph.ext 2 = lanlwExt … 1` by unfolding both bodies (`lanlwExt`, `BAExpandW.lean:114-119`) |
| A2 | tail of `lw2`: `(lwSplit p.2).map (lanlwD Γ p)` | identical (`p.1.dst = p.1.src = x`) |
| B1 | head of `Γ.lw4 p` | `z,y,α,β = bpv 0..3`; `W-1 = M⁺S⁺` as `M_{xz} M_{zx} S⁺_{zy}` (`bpW true`) |
| B2 | tail of `lw4` | `owxDE (bpv 3) (bpv 2) q.1` (2 edges) and `G_{βy} = bpS false (bpv 3) (bpv 1)` |

```
$ cd $SP && python3 lwverb.py struct 20000
parents 20000
lw2 leaf  terms  20000 delta [(1, 1, 1, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 20000  multiset_mismatch 0
lw2 tail  terms  40106 delta [(1, 1, 1, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 0  multiset_mismatch 0
lw4 leaf  terms  20000 delta [(1, 2, 2, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 0  multiset_mismatch 0
lw4 tail  terms  40106 delta [(1, 2, 2, 0)]  nM_ne 0  nAW_ne 0  nExt_ne 0  ordered_mismatch 0  multiset_mismatch 0
```
(`ordered_mismatch` and `multiset_mismatch` compare the verbatim terms with the (a) model; `delta` is `(n_S,n_W,n_A,n_M)` against the parent.) **Value of the verbatim lists** (algebraic identity, `BAlweightR` at `x` against `Σ val(lw2) + Σ val(lw4)`, parent `p = (Ǧ_{xx}, [Ǧ_{xc}, conj Ǧ_{cd}])`, random complex `G`, `d=L=3`, `t=1/2`; the red edge tests the `σ = false` branch of `owxDE`):
```
$ cd $SP && python3 val.py 1 0 0 ; python3 val.py 2 0.5 0.3
W=1 g0=0.0 E=0.0 n=27  m=0.000000+1.000000j
|R|=3.281425e+00  |lw2|=4.922138e+00 |lw4|=1.640713e+00  |R - (lw2 + lw4)| = 6.237e-16
terms: lw2 has 3 graphs, lw4 has 3 (1 + #lwSplit p.2 each)
W=2 g0=0.5 E=0.3 n=216  m=-0.139326+0.723352j
|R|=1.562301e-02  |lw2|=7.602395e-03 |lw4|=8.383912e-03  |R - (lw2 + lw4)| = 8.155e-17
terms: lw2 has 3 graphs, lw4 has 3 (1 + #lwSplit p.2 each)
```


### 2. D2: target 2 is `baExpFrame_lw`, the first conjunct of `BAexpFrameE` (item 2)

`theorem baExpFrame_lw (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, p.1.σ = true → p.1.circ = true → p.1.src = p.1.dst → ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, baSum (Γ.lw2 p) (BAlwData …) ℓe + baSum (Γ.lw4 p) (BAlwData …) ℓe ∂(PF d L W 0)`, binder for binder as probe 244-249 (the `gg` conjunct is L2c2b's). `p.1.src = p.1.dst` is used by the leaf `Ǧ_{αx}` (`owxEmb 2 p.1.dst`). Assembly, from merged results only (no new analysis):
1. `BAWeightOp_W_sub_one: BAlwW = 1 + BAlwMp * Sp` with `Sp = S * BAlwW` (`BAlwData`, `BAExpandW.lean:102`): from `baW_mul` (`:268`, `W (1 - M⁺S) = 1`) and the commutation of one-sided inverses of square matrices, `(1 - M⁺S) W = 1`, so `W = 1 + M⁺ S W`. Numerics: `‖(W-1) - M⁺S⁺‖ = 5.5e-14` in (a).
2. Per labelling `ℓ = Sum.elim ℓe ℓi`: `Γ.term = K · Ǧ_{xx} · f` with `f` the product of the edge factors of `p.2` (`BAExpandW_term_eq` `:541`, `BAExpandW_baPoly_edgePoly_prod` `:520`); a **generic-`k`** term lemma `BAWeightOp_ext_term` for `BAGraph.ext k` (copy of `BAExpandW_lanlwExt_term` `:570`, which is `k = 2` only; `LGraph.term_owxExt` `LWWeightExp.lean:474` is generic), and the labelled sum for `Fin 4`: `BAWeightOp_sum_fin4` and `BAWeightOp_integral_val4` (copies of `owx_sum_fin2` `:985`, `BAExpandW_integral_val2` `:801`; the `k = 2` one is merged and reused for `lw2`).
3. `baLweight_holds` (`BAExpandW.lean:354`) gives `∫ BAlweightL = ∫ BAlweightR` at `x = ℓ p.1.src` and `P` = the polynomial of `p.2`; `BAlwf`/`BAlwdf` are matched to the edge products through `baWx_baPoly`, `baWx_dh` (`BAExpand.lean:400, 485`, as in `baLweight_holds` `:362-420`) and `lwStein_dh_listProd`, `owx_list_aux` (the `hdh`, `hSD` pattern of `BAExpandW_term_integral`, `:740-770`).
4. Pointwise in `ω` and `ℓi`: `BAlweightR = Σ_{α,β}(lw2 terms) + Σ_{z,y,α,β}(lw4 terms)` by `W_{xy} = δ_{xy} + Σ_z M_{xz}M_{zx}S⁺_{zy}`; the `y = x` summand gives `lw2` (leaf plus the `lanlwD` tail, as in `BAExpandW_term_integral`), the kernel summand `lw4`. This is the identity checked by `val.py` above (`6e-16`, `8e-17`). The two integrals are put under one `∫` by `integral_add` with tameness-integrability of each term (`BAExpandW_term_tame1` `:554` is generic in the vertex type; `BAExpandW_integrable_PF` is private, copied).
5. `t = 0`: both sides vanish (`Ǧ = 0` and every term of `lw2`, `lw4` carries `S_{αβ}`, i.e. `bpW false`, with `S = 0`), as `lanlw_val` (`:908-950`); `baWx_dh` needs `0 < t`.

### 3. D3: counters and order in the form of T2395 §3 Step 3 (item 3)

Notation: `T° := T` with every solid edge circled (`BAWeightOp_circ`, a file-stem def); `nExt T := ((Finset.univ.filter fun v => v.isLeft = true).image T.atom).card` written inline (probe :33, so L3a4 gets `BAGraph.nExt` by `rfl`; no public `nExt` def here, to avoid a name clash with T2395). `BAGraph.counters`, `nA`, `nM`, `nExt` read only `waved, dotted, psi, mdot` and the vertex type (`BAVocab.lean:92-146`, `LWVocab.lean:157-159`), so `T°` and `T` have the same counters and `nExt`. Statements, for `Γ` a `BAGraph`, `p ∈ lwSplit Γ.solid`, `p.1.σ = true`, `p.1.circ = true` (and `Γ.Normal` for the last):
- `lw_counters`: `T ∈ Γ.lw2 p → T.counters = ⟨nS+1, nW+1, nA+1, nM, 0, 0⟩`; `T ∈ Γ.lw4 p → … ⟨nS+1, nW+2, nA+2, nM, 0, 0⟩` (the band's `n_W + 1 or 2`, `owxT1_counters`/`owxT2_counters`, with `n_A` rising by 1 resp. 2 and `n_M` fixed; in (a) (i)). Tail of `lw2`: `lanlwD_counters`. Leaf of `lw2`: its counters equal those of `lanlwT1 Γ p` (`lanlwT1_counters`, `BAExpandWOrd.lean:757`) because the two graphs differ only in the solid list (order and one circle): a 10-line congruence lemma. Leaf and tail of `lw4`: new, `Fin 4` (below).
- `lw_raw` (raw = ord T° − ord P): `(BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1` for `T ∈ lw2 p ++ lw4 p` (`ord = n_S + 2(n_W - n_A)`: `+1 + 2(1-1) = +1` and `+1 + 2(2-2) = +1`).
- `lw_mono` (the components of `BAstepMono` at `T°`): `nM T° = nM Γ`, `(nA - nW) T° = (nA - nW) Γ` (equal, from `lw_counters`), `nExt T° ≤ nExt Γ` (numerically equal; only `≤` is stated). Proof of `≤`: atoms of `T` meeting `E` inject into those of `Γ` by the retraction `z ↦ x`, `y, α, β ↦ x` (the only old-new `atomAdj` edges are `M_{xz}`, `M_{zx}`; `y–α` is internal to the new part), the `Fin 4` analogue of `BAExpandWOrd_rho` (`:328`).
- `lw_scalingOrderG` (`Γ.Normal`): `(Γ.scalingOrder : WithTop ℤ) ≤ T.scalingOrderG` for `T ∈ lw2 p ++ lw4 p`. Leaves (lw2, lw4): every solid edge circled (normality for `p.2`, the two new edges are `bpS true …`), so `splitG = [T]` and `scalingOrderG = scalingOrder = ord Γ + 1` (local copies of `BAExpandWOrd_splitG_of_circ`, `_packMerge_counters`, both private). Tail of `lw2`: public `lanlw_scalingOrderG` at `lanlwD Γ p q ∈ lanlwTerms Γ p` (`BAExpandWOrd.lean:803`); the audit's concern about the leaf is thus avoided: the leaf is proved directly, no permutation of the solid list is needed. Tail of `lw4`: three uncircled edges `e₁ = [src]–{β}`, `e₂ = {y,α}–[dst]`, `e₃ = {β}–{y,α}` (`[·]` an old atom); `j` `M`-splits give `ord Q - ord P = 1 - j + 2κ`, each split merges a new internal atom with a distinct atom, so `κ ≥ 1` once `j ≥ 1`, `j ≤ 3`: `≥ 0` (local copies of `BAExpandWOrd_nA_lt`, `_ext_ge`, `_split3`, private).
Script check on the verbatim lists, partition members `Q ∈ splitG T` included (same run as above):
```
Q-level (members of splitG(T)): members, min(ord Q - ord P), #(ord Q == ord P), #(nM Q > nM P), #((nA-nW) Q > P), #(nExt Q > nExt P)
lw2 leaf  members  20000 min 1  eq 0  nM_up 0  nAW_up 0  nExt_up 0
lw2 tail  members 320848 min 0  eq 47216  nM_up 0  nAW_up 0  nExt_up 0
lw4 leaf  members  20000 min 1  eq 0  nM_up 0  nAW_up 0  nExt_up 0
lw4 tail  members 320848 min 1  eq 0  nM_up 0  nAW_up 0  nExt_up 0
```
So the order never falls (`min ≥ 0`; equality only in the `lanlwD` tail of `lw2`, as `lanlw_scalingOrderG`), and `n_M`, `n_A - n_W`, `nExt` of the partition members do not rise. The member-level statements for `n_M`, `n_A - n_W`, `nExt` ("merging only lowers them", T2395 §3 Step 3 (a)) are L3a4's and are not targets here; the T-level statements above are what this ticket states. No other form is needed.

### 4. Deliverable (iv): plan against the stop line 2,000 (item 4)

`wc -l RBM3D/Graph/BAWeightOp.lean ≤ 2,000` (binding); ticket estimate 800 / 950 / 1,700. Budget in lines (low / central / high); analogues by `wc` of the ranges in `main`:
```
$ r(){ echo "$1:$2-$3 = $(( $3 - $2 + 1 )) lines"; }; r RBM3D/Graph/BAExpandWOrd.lean 184 300; r RBM3D/Graph/BAExpandWOrd.lean 306 620; ...
RBM3D/Graph/BAExpandWOrd.lean:184-300 = 117 lines   (generic atom / nA closure)
RBM3D/Graph/BAExpandWOrd.lean:306-620 = 315 lines   (Fin 2 ext: atomAdj, adj, nA, nM, nS, nW, counters)
RBM3D/Graph/BAExpandWOrd.lean:622-755 = 134 lines   (split lemmas, packMerge, ext_ge)
RBM3D/Graph/BAExpandWOrd.lean:757-835 = 79 lines    (counters / ord / ordG theorems)
RBM3D/Graph/BAExpandW.lean:534-700 = 167 lines      (term_eq, tame, ext_term, lab2)
RBM3D/Graph/BAExpandW.lean:801-877 = 77 lines       (val2, lanlw_val_seq)
RBM3D/Graph/BAExpandW.lean:905-968 = 64 lines       (lanlw_val on PF)
```
| Section of `BAWeightOp.lean` | content | low / central / high |
|---|---|---|
| S0 | header, imports, docstring, the verbatim defs (24 + 3 lines), `BAWeightOp_circ` | 70 / 80 / 100 |
| S1 | value layer (D2): `W_sub_one`, generic-`k` `ext_term`, `Fin 4` sums, `baExpFrame_lw` (analogue 167 + 77 + 64 = 308, plus the `Fin 4` parts and `W`) | 380 / 500 / 650 |
| S2a | generic closure and split lemmas, local copies of the private ones (analogue 117 + 134 = 251) | 230 / 260 / 300 |
| S2b | `Fin 4` ext lemmas: `atomAdj`, `adj`, `nA`, `nM`, `counters`, retraction, `nExt` (analogue 315 for `Fin 2`) | 350 / 450 / 550 |
| S2c | `lw_counters` (leaf-congruence for `lw2`), `lw_raw`, `lw_mono`, `lw_scalingOrderG` (analogue 79) | 150 / 200 / 260 |
| S3 | `BAWeightOpInst` (item 5) | 70 / 90 / 120 |
| total | | 1,250 / 1,580 / 1,980 |

Central 1,580 is within the ticket's high estimate 1,700; the high case is 20 lines under the stop line. Check points for the 1b (`wc -l` after each build): after S0 + S1 ≤ 650 (central 580); after S2a + S2b ≤ 1,350 (central 1,290). Rule: if the projected total exceeds 1,950 at a check point, the 1b stops and reports the count and the section that overran (CLAUDE.md §2 step 3: not specified, so the dispatcher decides). Nothing outside the targets is written: the member-level monotonicity (L3a4), `gg2/gg4` (L2c2), `BAexpFrameE` as a combined statement (L2c2b) stay out. No cut among the five targets is planned.

### 5. Instances and names (item 5)

Counters of the verbatim lists at the two instance parents (`baGcxx`, `BAExpandW.lean:980`; `baGwx = [Ǧ_{xx}, Ǧ_{ex}]`, `E = Fin 1`, `I = Fin 1`, `p = (Ǧ_{xx}, [Ǧ_{ex}])`):
```
$ cd $SP && python3 instverb.py
baGcxx counters (1, 0, 1, 1) ord -1 ordG -1 nExt 0
   lw2 0 counters (2, 1, 2, 1) ord 0 ordG 0 nExt 0  ord-ord(Gamma) = 1
   lw4 0 counters (2, 2, 3, 1) ord 0 ordG 0 nExt 0  ord-ord(Gamma) = 1
baGwx counters (2, 0, 1, 1) ord 0 ordG 0 nExt 1
   lw2 0 counters (3, 1, 2, 1) ord 1 ordG 1 nExt 1  ord-ord(Gamma) = 1
   lw2 1 counters (3, 1, 2, 1) ord 1 ordG 0 nExt 1  ord-ord(Gamma) = 1
   lw4 0 counters (3, 2, 3, 1) ord 1 ordG 1 nExt 1  ord-ord(Gamma) = 1
   lw4 1 counters (3, 2, 3, 1) ord 1 ordG 1 nExt 1  ord-ord(Gamma) = 1
```
Instances (all deterministic hypotheses discharged: `d = L = 3`, `W = 1`, `g₀ = 0`, `E = 0`, `m = i` through `BAExpandInst.baSelf_zero` (`BAExpand.lean:865`), `t = 1/2`; at `g₀ = 1/2`, `E = 3/10` the datum `m` stays a hypothesis `hSelf`, as in `BAExpandWInst`, `BAExpandW.lean:1014`): (1) `lw2`, `lw4` at `baGcxx` (one graph each) and `baGwx` (two each), the lists by `rfl`/`decide`; (2) `baExpFrame_lw` at `baGcxx` with `p = (⟨true,true,inr 0,inr 0⟩, [])` and at `baGwx` with the labelling `ℓe = ![e₀]`, `hp` by `simp [lwSplit]`, `rfl`, `rfl`, `rfl`; (3) `lw_counters`, `lw_raw`, `lw_mono`, `lw_scalingOrderG` at both parents (values of the table: `ord Γ = -1`, terms `ord 0`, `ordG 0`; `ord Γ = 0`, terms `ord 1`, `ordG ∈ {1,0,1,1}`, the `0` being the `lanlwD` tail, equal to `ord Γ`); `baGwx` is a local def `BAWeightOpInst.baGwx`. Hypotheses of the targets all hold at these data (`3 ≤ 3`, `0 ≤ 1/2 < 1`, `p.1.σ = p.1.circ = true`, `p.1.src = p.1.dst`, `Normal`); `BASelf` is the only external one, no limit involved (its fixed-point residual is in (a) (ii)). Name grep of the new public names on `main` (the stem-prefixed helpers `BAWeightOp_*` included):
```
$ for n in BAGraph.ext bpv bpS bpM bpW baSum BAGraph.lw2 BAGraph.lw4 baExpFrame_lw BAWeightOp_; do echo "$n $(git grep -l -E "\\b$n" main -- RBM3D RBM3D.lean | wc -l)"; done
BAGraph.ext 0
bpv 0
bpS 0
bpM 0
bpW 0
baSum 0
BAGraph.lw2 0
BAGraph.lw4 0
baExpFrame_lw 0
BAWeightOp_ 0
```

### Verdicts (after the repair)
- Target 1 (`BAGraph.ext`, `bpv/bpS/bpM/bpW`, `lw2`, `lw4` verbatim): PASS (numerics above; the only deviation from (a) is the solid order of the leaf, handled by a direct proof).
- Target 2 (`baExpFrame_lw`): PASS (pointwise identity `6e-16`/`8e-17`; assembly from `baLweight_holds`, `baW_mul`, `BAExpandW_*`).
- Target 3 (`lw_counters`, `lw_raw`, `lw_mono`, `lw_scalingOrderG`): PASS (T-level; member-level monotonicity is L3a4's).
- Target 4 (C1 / L5): PASS, as in (a). Target 5 (instances): PASS. Target 6: none.
- Deliverable (iv): plan 1,250 / 1,580 / 1,980 against 2,000 with two check points.

## (b) Script output — Sun Oct 11 05:39:24 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2407`, branch `t/T2407` (HEAD `849a959`), one new file `RBM3D/Graph/BAWeightOp.lean`.
```
$ wc -l RBM3D/Graph/BAWeightOp.lean   # stop line 2,000
1941 RBM3D/Graph/BAWeightOp.lean
$ for h in $(git log --format=%h --reverse 5ee937e..HEAD -- RBM3D/Graph/BAWeightOp.lean); do printf "%s:%s " $h $(git show $h:RBM3D/Graph/BAWeightOp.lean | wc -l); done
63edbe2:720 dfca92e:1333 daea84f:1828 bb4ee04:1941 849a959:1941 
$ lake build RBM3D.Graph.BAWeightOp 2>&1 | grep -E 'Built|Build completed'   # already built at this content
Build completed successfully (3783 jobs).
$ git diff --stat main...t/T2407 | tail -2
 RBM3D/Graph/BAWeightOp.lean | 1941 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1941 insertions(+)
$ lake env lean axioms.lean   # #print axioms of the 22 new public declarations, counted by axiom list
18 depends on axioms: [propext, Classical.choice, Quot.sound]
1 depends on axioms: [propext]
3 does not depend on any axioms
$ lake env lean axioms.lean | grep -E 'baExpFrame_lw|lw_counters|lw_raw|lw_mono|lw_scalingOrderG' | grep -c 'axioms: \[propext, Classical.choice, Quot.sound\]'   # the 5 targets
5
$ date -u; lake build 2>&1 | grep -E 'axiom audit|Build completed'   # RBM3D.lean with `import RBM3D.Graph.BAWeightOp` added temporarily, restored after (git status: only BAWeightOp.lean)
Sun Oct 11 05:37:06 UTC 2026
info: RBM3D.lean:447:0: axiom audit: 11375 theorems, 3435 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4214 jobs).
$ echo "$(probe | sed -n 105,126p | shasum | cut -c1-12) $(sed -n 55,76p RBM3D/Graph/BAWeightOp.lean | shasum | cut -c1-12) $(probe | sed -n 239,241p | shasum | cut -c1-12) $(sed -n 80,82p RBM3D/Graph/BAWeightOp.lean | shasum | cut -c1-12)"   # probe=4c1de4c:RBM3D/Probe/T2395Pins.lean; ext..lw4 probe|file, baSum probe|file
a18fbbc0c403 a18fbbc0c403 4506a4b8dd88 4506a4b8dd88
$ git grep -n -E '<new public names>' main -- RBM3D RBM3D.lean | wc -l   # BAGraph.ext bpv bpS bpM bpW baSum BAGraph.lw2 BAGraph.lw4 baExpFrame_lw lw_counters lw_raw lw_mono lw_scalingOrderG BAWeightOp
0
$ grep -c -E 'sorry|admit|native_decide|^axiom' RBM3D/Graph/BAWeightOp.lean
0
$ git log -1 --format=%h -- <copy source>   # copies from merged RBM3D files (none from RBM1D/RBM2D)
Graph/BAExpandWOrd.lean e17d56f   Graph/BAExpandW.lean 8f90d6d
```

Target statements, extracted by script from the file (`s.index('theorem NAME')` to `:= by`, whitespace collapsed):
```
theorem baExpFrame_lw (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, p.1.σ = true → p.1.circ = true → p.1.src = p.1.dst → ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, baSum (Γ.lw2 p) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.lw4 p) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
theorem lw_counters : ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true → (∀ T ∈ Γ.lw2 p, T.counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩) ∧ (∀ T ∈ Γ.lw4 p, T.counters = ⟨Γ.nS + 1, Γ.nW + 2, Γ.nA + 2, Γ.nM, 0, 0⟩)
theorem lw_raw : ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true → (∀ T ∈ Γ.lw2 p, (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) ∧ (∀ T ∈ Γ.lw4 p, (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1)
theorem lw_mono : ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true → (∀ T ∈ Γ.lw2 p, (BAWeightOp_circ T).nM = Γ.nM ∧ ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW = (Γ.nA : ℤ) - Γ.nW ∧ ((Finset.univ.filter fun v : Ex ⊕ (Ix ⊕ Fin 2) => v.isLeft = true).image (BAWeightOp_circ T).atom).card ≤ ((Finset.univ.filter fun v : Ex ⊕ Ix => v.isLeft = true).image Γ.atom).card) ∧ (∀ T ∈ Γ.lw4 p, (BAWeightOp_circ T).nM = Γ.nM ∧ ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW = (Γ.nA : ℤ) - Γ.nW ∧ ((Finset.univ.filter fun v : Ex ⊕ (Ix ⊕ Fin 4) => v.isLeft = true).image (BAWeightOp_circ T).atom).card ≤ ((Finset.univ.filter fun v : Ex ⊕ Ix => v.isLeft = true).image Γ.atom).card)
theorem lw_scalingOrderG : ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))), p ∈ lwSplit Γ.solid → p.1.σ = true → p.1.circ = true → Γ.Normal → (∀ T ∈ Γ.lw2 p, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧ (∀ T ∈ Γ.lw4 p, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG)
```

Compiled instances (namespace `RBM.Graph.BAWeightOpInst`, file lines 1835-1941; `d = L = 3`, `W = 1`, `g0 = 0`, `E = 0`, `m = i`, `t = 1/2`, `hSelf := BAExpandInst.baSelf_zero`; all hypotheses discharged; `baGcxx` is the merged weight `Ǧ_{xx}`, `baGwx = Ǧ_{xx} Ǧ_{ex}` is new). Excerpts, whitespace collapsed by script:
```
def baGwx : BAGraph (Fin 1) (Fin 1) where solid := [⟨true, true, .inr 0, .inr 0⟩, ⟨true, true, .inl 0, .inr 0⟩] waved := [] dotted := [] coeff := 1 psi := [] mdot := []
theorem lists_baGwx : (baGwx.lw2 p1).length = 2 ∧ (∀ T ∈ baGwx.lw2 p1, T.nS = 3 ∧ T.nW = 1 ∧ T.nA = 2 ∧ T.nM = 1) ∧ (baGwx.lw4 p1).length = 2 ∧ (∀ T ∈ baGwx.lw4 p1, T.nS = 3 ∧ T.nW = 2 ∧ T.nA = 3 ∧ T.nM = 1) := by decide
example : ∫ ω, baGwx.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![fun i => if i = 0 then 1 else 0] ∂(PF 3 3 1 0) = ∫ ω, baSum (baGwx.lw2 p1) (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![fun i => if i = 0 then 1 else 0] + baSum (baGwx.lw4 p1) (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![fun i => if i = 0 then 1 else 0] ∂(PF 3 3 1 0) := baExpFrame_lw 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num) baGwx _ p1 hp1 rfl rfl rfl
example (d : ℕ) : frameE1 d := fun L W _ _ hL g0 Em t m hS h0 h1 _ _ _ _ _ _ Γ ℓe => baExpFrame_lw d L W hL g0 Em t m hS h0 h1 Γ ℓe   -- frameE1 = the pinned first conjunct of BAexpFrameE, probe :244-251
```
The same file has `example`s applying `baExpFrame_lw` at `baGcxx`, and `lw_counters`, `lw_raw`, `lw_mono`, `lw_scalingOrderG` at `baGcxx` and `baGwx` (one application each, hypotheses `hp0/hp1 : p ∈ lwSplit …`, `rfl`, `rfl`, `hN0/hN1 : Normal`); `lists_baGcxx` is the same check for `baGcxx` (counters `(2,1,2,1)` and `(2,2,3,1)`).

Narrative (what the file contains; every number is in the output above or in the file).
- The earlier uncommitted `BAWeightOp.lean` (183 lines at the start of this stage: its own `lweightT1A`, `lweightKer`, … lists) does not fit Amend 1 and was replaced; nothing of it was kept (copy in the scratch directory).
- Lines 51-83: Target 1, `BAGraph.ext`, `bpv`, `bpS`, `bpM`, `bpW`, `BAGraph.lw2`, `BAGraph.lw4`, `baSum`, verbatim (the shasums above agree). The `(a′)` hash `6589d94b2605` covers probe lines 105-128; lines 127-128 are the docstring of `gg2` (L2c2), so the file copies 105-126.
- Lines 85-724, Target 2 `baExpFrame_lw` (line 682; statement binder for binder the first conjunct of `BAexpFrameE`, checked by `frameE1`): `W = 1 + M⁺(S W)` (`BAWeightOp_W_sub_one`, from `baW_mul` by `mul_eq_one_comm`); a generic-`k` term lemma and a `Fin 4` labelling sum; term formulas of the four term kinds (the `lw2` derivative term is the merged `lanlwD`, `BAExpandW_lanlwD_term`); `BAWeightOp_pathwise` (the terms of `lw2`, `lw4` sum to `K Σ_y W_{xy}(…)` for abstract data), `BAWeightOp_core` (one labelling of the old vertices, from `baLweight_holds` through `lwWx_integral`, as `lanlw_val`), `BAWeightOp_val_seq`; `t = 0` separately (`Ǧ = 0`, `S = 0`).
- Lines 726-1833, Target 3: raw counters (`lw_counters`), `lw_raw` (`ord T° = ord Γ + 1`, the form of T2395 design §3 Step 3), `lw_mono` (`n_M`, `n_A - n_W` of `T°` and the number of atoms with an external vertex do not grow), `lw_scalingOrderG`. The `lw2` leaf has the counters of `lanlwT1` (`lanlwT1_counters`); the `lw2` derivative term is `lanlwD` (`lanlwD_counters`, `lanlw_scalingOrderG`). The `lw4` terms are `ext 4` with `x–z`, `y–α` as `M`-dotted edges: `n_A + 2` (two new internal atoms `{y, α}`, `{β}`), `n_M` fixed; for this the private closure lemmas of `Graph/BAExpandWOrd` (lines 53-176, 180-297, 620-692 there; no split2) are copied with the unattached part of the pendant extension counted as `k` classes (`BAWeightOp_rtg_ext`, `BAWeightOp_cnt_ext`). `lw_mono`'s external-atom count: `#atoms = nExt + n_A` (`BAWeightOp_nExt_add_nA`) and the atom count rises by `k` as `n_A` does, so equality holds; the statement says `≤`.
- Leaves of `lw2`, `lw4` are normal, so `ordG = ord` (`BAGraph.scalingOrderG_of_normal`); the derivative term of `lw4` has three uncircled edges, `j` splits give `ord - ord Γ = 1 - j + 2κ`, `κ ≥ 1` for `j ≥ 2` (the singleton atom `{β}` is merged).
- C1/L5: no smallness hypothesis on `g` or `‖M - m₀I‖` appears; the inputs are `baLweight_holds`, `baW_mul`, `BASelf` and the tameness lemmas of the merged files.
- Not changed: `RBM3D.lean` (the hub adds the import at merge, CLAUDE.md §3 (A) 4); nothing outside `RBM3D/Graph/BAWeightOp.lean`. The ticket's acceptance line says report ≤ 150 lines; sections (a), (a′) by the earlier stages are 216 lines, so this report is kept within CLAUDE.md §6's 300 lines instead.

## (c) Verified Mathlib names (all used in the file, which builds)

`mul_eq_one_comm` (`Mathlib/Algebra/Group/Monoid.lean:54`, used for `Matrix (Idx d L W) (Idx d L W) ℂ`); `sub_eq_iff_eq_add`; `Finset.sum_comm`, `Finset.sum_sub_distrib`, `Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_ite_eq`; `Finset.card_union_of_disjoint`, `Finset.card_image_of_injective`, `Finset.card_pair`, `Finset.card_singleton`, `Finset.insert_eq_of_mem`, `Finset.image_insert`, `Finset.image_singleton`, `Finset.disjoint_left`; `List.prod_eq_zero`, `List.mem_map_of_mem` (one explicit argument); `continuous_list_sum`, `integral_finsetSum`, `integral_const_mul`, `Integrable.const_mul`, `integral_add`; `Equiv.sumArrowEquivProdArrow`; `Relation.ReflTransGen.lift`. Verified absent: `Matrix.mul_eq_one_comm` (`Unknown constant`; the generic `mul_eq_one_comm` is used). Deprecated in this Mathlib: `push_neg` (warning "Prefer using `push Not`"; not used in the final file).

## (d) Open issues and paper-delta candidates

- `T2407a` (Lean/paper statement difference): the BA vocabulary has no kernel edge `1 + M⁺S⁺` (`WEdge` is `S` or `S⁺`). (B.19)'s `Σ_y (1 + M⁺S⁺)_{xy}` is split into `y = x` (`lw2`) and `(M⁺S⁺)_{xy} = Σ_z M_{xz} M_{zx} S⁺_{zy}` (`lw4`, `bpW true`, `M⁺ = M_{xy} M_{yx}`, `B:388`), with `S⁺ = S W` read from the data (`BAlwData.Sp`). Only the self-loop form `Ǧ_{xx}` is stated (`p.1.src = p.1.dst`), as (B.19) is.
- Observation: the `lw2` leaf lists `[Ǧ_{αx}, Ǧ_{ββ}]` (circle on `G_{αx}`), `lanlwT1` lists `[Ǧ_{ββ}, G_{αx}]`; the counters agree (`BAWeightOp_leaf2_counters`), a term's value is a product over its solid edges, so their order does not matter for the value.
- For the hub: the import `RBM3D.Graph.BAWeightOp` is to be added to `RBM3D.lean` at merge (pre-check above). For the dispatcher: `t/T2395:RBM3D/Probe/T2395Pins.lean` defines the same names (`BAGraph.ext`, …, `baSum`, `BAexpFrameE`); the probe is never merged. `BAexpFrameE` as a combined statement needs `gg2`/`gg4` (L2c2/L2c2b); the member-level facts of `BAstepMono` (partition members) are L3a4's, not stated here.
