Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 01:03:56 UTC 2026

Sources read: ticket + check file `docs/tickets/checks/T2432-check.lean` (CONTROL line 57: compiled on main fff8d03, exit 0); `LWSymm:160-200, 545-575, 1212-2326`;
`BASymm1` (whole); `BAExpandW:107-148, 898-916`; `BAWeightOp:53-83, 676-690, 1645-1830`; `BAGGOp:69-93, 834-852, 1608-1720`; `BAExpandWOrd:776-810`;
`BAVocab:55-100, 136-240, 1154-1170`; `BA/CouplingWindow:855-872`; probe `t/T2395:RBM3D/Probe/T2395Pins.lean:140-300`; `LWProv:942-1077`; design `T2395-design.md:78-90, 104-160`.

### (i) Exponent table (no scaling exponent enters; constants, hypotheses and counter increments)

| item | value | constraint | slack / status |
|---|---|---|---|
| `BASelf d L g0 Em m`, `0 ≤ t < 1`, `3 ≤ L` | hypotheses of targets 2-3 | needed only by `lanlw_val`, `baExpFrame_lw`, `baExpFrame_gg` (inside the frame identity) | not used by targets 1, 2, 4 (`baTwistIntegral_holds` uses none, `BASymm1:407`); C1: no smallness of `g0`, no `M a b = 0`, no `M a a = m` |
| `g0` | any real | `BAlwData` has `S` real, `gPsi = g0 Ψ` real (`BASymm1_data_real`, `BASymm1:299`) | real `g0` suffices; instance `g0P = 4.672` |
| selector `(c,t')` | `lwSymmTwistS c t' e = ⟨σ xor c, circ, (t' ? dst : src), (t' ? src : dst)⟩` (`LWSymm:1969-1972`) | `σ(twistS p.1) = true`, `circ` kept (`lwSymmTwistS_circ :1230`) | the hypotheses of (a)-(c) are on the twisted edge; `lanlw_val` needs `p.1.σ = true`, `p.1.circ = true` at the frame (`BAExpandW:908-912`), so every hypothesis is met exactly, slack 0 and nothing extra |
| (a) loop | `src = dst` | `lwSymmTwistS_loop` (`LWSymm:2006`): `src = dst` iff twisted `src = dst` | equal |
| (c) pair | `(twist p.1).src = (twist q.1).dst` | `baExpFrame_gg` hypothesis `p.1.src = q.1.dst` at the frame (`BAGGOp:785`) | equal; `q ∈ lwSplit p.2` becomes `twistP q ∈ lwSplit (p.2.map twistS)` by `lwSymm_lwSplit_twistP` (`LWSymm:1568`) |
| counters `lw2` / `lw4` (frame) | `⟨nS+1, nW+1, nA+1, nM,0,0⟩` / `⟨nS+1, nW+2, nA+2, nM,0,0⟩` (`lw_counters`, `BAWeightOp:1680`) | `ord = nS + 2(nW - nA)`: `+1` each | tight (`lw_raw`) |
| counters `lanlw` | `⟨nS+1, nW+1, nA+1, nM,0,0⟩`, `ord+1` (`lanlw_ord`, `BAExpandWOrd:781`) | | tight |
| counters `gg2`, `gg4` | `A1: ord Γ + 2κ`; every other term `ord Γ + 1` (`gg_raw`, `BAGGOp:1636`) | | `κ ∈ {0,1}`: `A1` keeps the order iff `κ = 0` |
| twist of a term `T` | `(T.twist c t).counters = T.counters` (`ba_twist_counters`, `BASymm1:83`); `nExt`, `nLoops`, `nPairs`, `Normal` kept (`baTwistInv_holds`, `BASymm1:175`) | | equalities (slack 0) |
| `T°` (`BAWeightOp_circ`) | `BAWeightOp_circ (T.twist c t) = (BAWeightOp_circ T).twist c t` (solid: `lwSymmTwistS_with_circ :1234`, other fields untouched) | gives `lw_raw`, `lw_mono`, `gg_raw`, `gg_mono` for twisted outputs from the frame's | equality |
| integrability | none | `lwSymm_integral_cj` and `MeasurePreserving.integral_comp'` hold without it | target 2's integrand is one integral of `baSum A + baSum B` |
| stop line / split | 2,000 / 1,700 | predicted total below | see (vi) |

### (ii) One concrete nondegenerate instance

`d = 3`, `L = 4`, `W = 2` (`N = (W L)^3 = 512`), flow point `flowP` of `(L, g) = (4, 10)` (`BA/CouplingWindow.lean:855-869`, `flowP_data : 0 < t0P ∧ t0P < 1 ∧ BASelf 3 4 g0P EP m0P`).
Graph `Γ` (`E = {v0, v1}`, `I = {x}`): solid `Ḡ_{v0 x}` (red, circled, **the selected in-edge `p.1`**), `G_{x v1}`, `Ḡ_{v1 v0}` (all circled: normal); waved `S⁺_{v0 v1}` (coloured), `S_{v0 x}` (black);
`×`-dotted `v0 v1`; `Ψ`-edge `v1 x`; `M`-edge `M_{x v1}`; coeff `1 + i/2`. Selector `(c,t') = (true,true)`: the twisted edge is `G_{x v0}` (blue, circled, out-edge of `x`), the frame is `Γ.twist c t'`,
`lanlwTerms` has `1 + |lwSplit p'.2| = 3` terms (`x, α, β` internal). The script evaluates `BAGraph.val` literally (`SEdge.val`, `WEdge.val`, `BAMEdge.val`, `BAPsiEdge.val`; `LWVocab:115-134`, `BAVocab:64-81`),
builds the terms by the definitions `lanlwExt/T1/D` (`BAExpandW:114-148`), `owxDE` (`LWWeightExp:468`) and the twist (`BASymm1:65-71`, `LWSymm:93-96, 164-172`), and checks the pathwise identity of target 2
`baSum (T.map twist) (D ω) = cj^c (baSum T (D^{t'} ω))` at one sample `ω` of `PF 3 4 2 0` (all four twists), plus target 1 (`twist twist = id`). Numerics only; no Lean.

```
$ cd <scratchpad>/T2432 && python3 -u inst.py     # <scratchpad> = /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad ; numpy, 129 lines
flowP: t0=0.218307 E=-0.000000 g0=4.672337 m0=0.000000+0.560680i ; Im m0>0: True ; BASelf residual 3.33e-16 ; 0<t0<1: True ; 3<=L: True
N=512  M offdiag max 0.5546  |M-M^T| 2.2e-15  |Sp-Sp^T| 2.9e-15
G(flip w) = G(w)^T : 1.02e-14
graph: solid [(False, True, 0, 2), (True, True, 2, 1), (False, True, 1, 0)] ; p.1 = red circled in-edge of x=2 (sigma=False, circ=True, src=v0, dst=x); Normal: True
twist_invol: {(False, False): True, (False, True): True, (True, False): np.True_, (True, True): np.True_}
selector (c,t')=(T,T): twist p.1 = (True, True, 2, 0) = blue circled out-edge of x=2 with far end v0; hypotheses of (b): sigma=True, circ=True
lanlwTerms of the frame: 3 terms (1 + |lwSplit p'.2| = 2 )
target 2 pathwise (c,t')=(T,T): baSum(terms.map twist)(D w) = 2.913772e-13+1.116651e-13i ; cj baSum(terms)(D^t w) = 2.913772e-13+1.116651e-13i ; rel.err 0.00e+00
   against D(flip w) (G recomputed at X^T): rel.err 1.73e-13
   (c,t')=(False,False): rel.err 0.00e+00   (first term of the frame list has 4 solid edges)
   (c,t')=(False,True): rel.err 0.00e+00   (first term of the frame list has 4 solid edges)
   (c,t')=(True,False): rel.err 0.00e+00   (first term of the frame list has 4 solid edges)
val(Gamma, D w) = -6.485246e-14+1.419608e-12i ; val(F, D w) = -1.064632e-12+9.413028e-13i
```
Reading: every hypothesis of target 3(b) holds at once at this graph (`σ = true`, `circ = true` after the twist, `p ∈ lwSplit Γ.solid`), `BASelf` residual `3.3e-16`, `0 < t0 = 0.218 < 1`, `3 ≤ 4`; the values are nonzero
(`~1e-13`, small because the products carry `S ~ t/16`, `Ψ`, `M` factors; relative errors, not absolute, are the test). The `rel.err 0` against `D^t = (Gᵀ, Mᵀ, Sᵀ, Spᵀ, Ψᵀ)` is exact because the same
arithmetic is run on transposed arrays; the independent comparison against `D(flip ω)` (a second inversion at `Xᵀ`) is `1.7e-13`. The script does not evaluate the Gaussian expectation (the frame identity `lanlw_val` is merged, `BAExpandW:908`);
the instance checks the new content (pathwise twist of a list of frame terms). External hypothesis: none (`BASelf` is discharged by `flowP_data`; no external input).

### (iii) Section map `LWSymm` §5-§6 → `BASymm2` (planned; `BASymm2_` = private stem)

| `LWSymm` | planned `BASymm2` declaration | S′ |
|---|---|---|
| 181 `lwSymmTwistG_invol` | **target 1** `BAGraph.twist_invol` (`toLGraph` by `lwSymmTwistG_invol`; `psi`, `mdot` by `BAPsiEdge/BAMEdge.twist` involutions: σ flips twice, ends swap twice) | new |
| 1224-1237 `lwSymm_lwSplit_map`, `lwSymmTwistS_circ`, `_with_circ` | imported (public) | none |
| 1239-1303 `Uncirc`, `Frame*` defs | not needed: the frame is `Γ.twist c t'` at `lwSymmTwistP c t' p` (no uncircling) | drop |
| 1306-1386 `FormDefs` (16 output defs) | replaced by `lanlwTerms`, `lw2/lw4`, `gg2/gg4` of the frame `.map (BAGraph.twist c t')` | drop |
| 1388-1475 `Uncirc` (`hX`, `M a b = 0`) | dropped (BA acts on circled edges; F5) | drop |
| 1477-1512 `FrameCounters` | dropped (no uncircling) | drop |
| 1516-1562 `DataFacts` | now `BASymm1_data_real`, `BASymm1_Sp_symm`, `baM_symm` | drop |
| 1564-1576 `Transport` (`lwSymm_lwSplit_twistP`, `lwSymm_cj_list_sum`) | imported | none |
| 548-575 `lwSymm_twist_integral` | **target 2** `baSum_twist` (pathwise: `baSum (A.map twist) D ℓe = cj^c (baSum A (BASymm1_dataTr D t') ℓe)` for real `D`, from `BAGraph.BASymm1_val_twist`), `baTwistIntegral_gen` (any `F : BALData (Idx d L W) → ℂ`: `∫ cj^c F(Tr D ω) = cj^c ∫ F(D ω)`), `BAtwistSum`, `baTwistSum_holds` | new, ~90 |
| 1578-1624 `lwSymm_weight_graph_E` | **target 3(a)** (`baExpFrame_lw` at the frame, `twist_invol`, `baTwistIntegral_holds`, `baTwistSum_holds`) | ~25 |
| 1626-1676 `lwSymm_oe1x_graph_E` | **target 3(b)** (`lanlw_val`, `B = []`, `baSum [] = 0`) | ~20 |
| 1678-1741 `lwSymm_oe2x_graph_E` | **target 3(c)** (`baExpFrame_gg`; `q' = twistP q ∈ lwSplit (twistP p).2`) | ~30 |
| 1743-1961 `FormCounters` | **target 4**: `BASymm2_circ_twist` (`T°` commutes with the twist), `ba_twist_inv_out` (counters, `scalingOrder`, `nExt`, `nLoops`, `nPairs`, `Normal` of `T.twist`), then one corollary per form (`lw`, `lanlw`, `gg`) giving `lw_raw`, `lw_mono`, `gg_raw`, `gg_mono`, `lanlw_ord` for the twisted outputs relative to `Γ` | new, ~150 |
| 1963-2032 `Selector` | imported (`lwSymm_twist_weight`, `lwSymm_selector_edge`, `lwSymm_selector_pair`) | none |
| 2034-2326 §6 instances | `BASymm2Inst`: three graphs (loop, edge, pair) with a `Ψ`- and an `M`-edge, memberships by `decide`, statement-level instances (target 5) | ~170 |

Reading fixed by this section: `lanlw_scalingOrderG`, `lw_scalingOrderG`, `gg_scalingOrderG` are stated for `T.scalingOrderG` (min over `T.partition`). They hold at the **frame** terms, relative to `Γ` (`(Γ.twist c t').scalingOrder = Γ.scalingOrder` by `ba_twist_counters`; `Normal` kept by `baTwistInv_holds`),
and that is what L3a4 needs, since `BALocStep` twists the **packed** partition members (`F.map (BAPGraph.twist c t)`, probe 207) and a packed twist keeps the counters. `scalingOrderG (T.twist c t) = scalingOrderG T` would need
`LGraph.partition (twist Γ) ≅ (partition Γ).map twist`, which is assigned to L3b4′ (`T2423-amend-1.md`, S1/O4); it is not a target and not proved here. Finding for the dispatcher (no statement changes).

### (iv) `LWSymm` §4 (`OwxE`, `:576-1211`) needs no twin

`lanlw_val` (`BAExpandW:908-916`) has hypotheses `p ∈ lwSplit Γ.solid`, `p.1.σ = true`, `p.1.circ = true`, `Γ : BAGraph Ex Ix` with no condition on `p.1.src : Ex ⊕ Ix`; `baExpFrame_lw` adds `p.1.src = p.1.dst`,
`baExpFrame_gg` adds `p.1.src = q.1.dst` (`BAGGOp:785`; `baExpFrame_lw`: `BAWeightOp:682`; both packed in `baExpFrameE_holds`, `BAGGOp:848`). The only vertex types are `Ex ⊕ Ix`, so external and internal endpoints are covered; `BAexpFrameE` is stated for every `d`. No `OwxE` twin.

### (v) Shapes used downstream

L3a3 (probe 254): `BAlvl1StepIdentity d : ∀ L W, 3 ≤ L → ∀ g0 Em t m, BASelf d L g0 (Em:ℂ) m → 0 ≤ t → t < 1 → ∀ {E} (P : BAPGraph E) (outs), BALocStep P outs → P.g.Normal → ∀ ℓe, ∫ P.val (BAlwData … ω) ℓe ∂PF = ∫ BAComb.val outs (BAlwData … ω) ℓe ∂PF`,
`BALocStep P outs := ∃ c t F, BAFrameStep (P.twist c t) F ∧ outs = F.map (BAPGraph.twist c t)` (probe 207). The macro sums are 3 lists (`withinOuts`: `outsOf (… :: (lwSplit p.2).map (BAGraph.lanlwD Γ p))`, `outsOf (tr.lw2 pp)`, `outsOf (tr.lw4 pp)`, probe 160-166) and 4 lists (`splitOuts`, probe 168-176).
How target 2 serves them: `BAComb.val` of twisted packed graphs is `cj^c (BAComb.val F (Tr D))` pathwise (`BASymm1_val_twist` at `h.choose`, R1's `BAPGraph.twist` keeps `ext`); the sum of `k` such lists is `cj^c` of one function `F(D) = Σ_k …` of the data, so `baTwistIntegral_gen`
(arbitrary `F`) gives the integral for any `k`; `BAtwistSum` is the `k = 2` instance the three frame forms use. The list types are free (`Iy`, `Iz` independent). L3d4 (twin of `LWProv:942-1109`): `lwProv_weight_EW'` (`:943`), `lwProv_edge_EW'` (`:1042`), `lwProv_gg_EW'` (`:1110`) are the forms with a real weight `W : (E ⊕ I → Idx) → ℝ`
(`lwProv_EW` = `Σ_ℓ W(ℓ) term`), each proved from the unweighted form and `lwProv_EW_twist`; the BA twin needs a weighted `val` twist lemma, which is L3d4's and not pinned here; `baTwistIntegral_gen` and `baSum_twist` are the unweighted inputs.

### (vi) Predicted lines (code and docstrings) against the stop line 2,000 per file

| block | lines |
|---|---|
| header, module doc, imports | 70 |
| target 1 | 25 |
| target 2 (`baSum_twist`, `baTwistIntegral_gen`, def, theorem) | 90 |
| target 3 (pinned statement 35, frame membership lemma 20, three proofs 75) | 130 |
| target 4 (circ-twist 20, outputs 30, three corollaries 100) | 150 |
| instances (three graphs, memberships, statement-level applications, `d = 3`, `L = 4`, `W = 2`, `flowP_data`) | 170 |
| **total** | **≈ 635** (code count of this table); T2395 §6 prices 750 / 850 / 1,470 and the ticket expects ≈ 800-1,300 |

Prediction 635-1,300 (the ticket's range) < 1,700: **`BASymm2B` is not needed.** If it were, the boundary is after target 3 (§3): `BASymm2` = targets 1-3, `BASymm2B` = target 4 and the instances (import `BASymm2 → BASymm2B`).

### Verdicts
1. Target 1 `BAGraph.twist_invol`: **PASS** (true; `lwSymmTwistG_invol`, `psi`/`mdot` involutions; checked at four twists in (ii)).
2. Target 2 `BAtwistSum` / `baTwistSum_holds` and the pathwise list form: **PASS** (pathwise identity checked in (ii); no integrability needed; `BASelf`, `0 ≤ t < 1` unused).
3. Target 3 `BAtwistFormE` / `baTwistFormE_holds`: **PASS** (each hypothesis is the frame hypothesis of `lanlw_val`, `baExpFrame_lw`, `baExpFrame_gg` after the twist; selectors imported).
4. Target 4 (counters, `scalingOrder`, `nExt`, `nLoops`, `nPairs`, `Normal` of twisted outputs; `lanlw_ord`, `lw_raw`, `lw_mono`, `gg_raw`, `gg_mono` relative to `Γ`): **PASS** under the reading of (iii) (no `scalingOrderG` of an unpartitioned twisted output).
5. Instances `d = 3`, `L = 4`, `W = 2`, `flowP_data`: **PASS** (nondegenerate, (ii)). 6. C1: **PASS**. 7. Registry: none; pre-check `import RBM3D` + `#assert_rbm_axioms`.
Overall: **PASS**

## (b) Script output (stage 1b, written Mon Oct 12 01:25:48 UTC 2026)

```
$ per-commit line counts (stop line 2,000 per file); final count; BASymm2B; git diff --stat main...t/T2432
450fb36      143 lines  T2432: BASymm2 targets 1-2 (twist_invol, baSum_twist, baTwistIntegral_
c59b4ed      252 lines  T2432: BASymm2 target 3 (BAtwistFormE, baTwistFormE_holds)
1cf089e      431 lines  T2432: BASymm2 target 4 (twisted outputs: counters, order, monotonicit
cf9ec0b      554 lines  T2432: BASymm2 instances (target 5) at d=3, L=4, W=2, flowP
     554 RBM3D/Graph/BASymm2.lean
ls: RBM3D/Graph/BASymm2B.lean: No such file or directory
 RBM3D/Graph/BASymm2.lean | 554 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 554 insertions(+)
# section map of (iii) as finally written (line numbers of BASymm2.lean found by script; (a) planned ~635 lines, landed 554)
$ python3 secmap.py
LWSymm:181 lwSymmTwistG_invol -> BAGraph.twist_invol:69
LWSymm:548-575 lwSymm_twist_integral -> baSum_twist:87 baTwistIntegral_gen:104 BAtwistSum:118 baTwistSum_holds:129
LWSymm:1224-1237, 1564-1576 (lwSplit maps, Transport; imported) -> BASymm2_frame_mem:148 BASymm2_pair_mem:155 BASymm2_frame_circ:161
LWSymm:1578-1741 (lwSymm_weight_graph_E, _oe1x_, _oe2x_) -> BASymm2_back:178 BASymm2_back1:192 BAtwistFormE:209 baTwistFormE_holds:236
LWSymm:1743-1961 FormCounters -> ba_twist_inv_out:258 BASymm2_circ_twist:265 BASymm2_mono:279 baTwist_lanlw_ord:311 baTwist_lanlw_scalingOrderG:321 baTwist_lw_raw:329 baTwist_lw_mono:342 baTwist_lw_scalingOrderG:360 baTwist_gg_raw:370 baTwist_gg_mono:391 baTwist_gg_scalingOrderG:419
LWSymm:2034-2326 (§6 instances) -> namespace BASymm2Inst at 431-554
LWSymm:1963-2032 Selector: imported, not called; dropped as (iii) planned: 1239-1303 Frame, 1306-1386 FormDefs, 1388-1475 Uncirc, 1477-1512 FrameCounters, 1516-1562 DataFacts
# targets 2-3 against the check file: the def blocks with the names replaced by NAME, diff; then the statements extracted by script (line:text)
$ python3 extract.py; diff T2432_TwistSum.chk BAtwistSum.mine; diff T2432_FormE.chk BAtwistFormE.mine
== T2432_TwistSum vs BAtwistSum
IDENTICAL
== T2432_FormE vs BAtwistFormE
IDENTICAL
$ python3 decls.py BAGraph.twist_invol baTwistIntegral_gen BAtwistSum baTwistSum_holds BAtwistFormE baTwistFormE_holds
69:theorem BAGraph.twist_invol (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).twist c t = Γ := by
104:theorem baTwistIntegral_gen (g0 Em t : ℝ) (m : ℂ) (c t' : Bool) (F : BALData (Idx d L W) → ℂ) :
105:    ∫ ω, lwSymmCj c (F (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t')) ∂(PF d L W 0) =
106:      lwSymmCj c (∫ ω, F (BAlwData d L W g0 Em t m ω) ∂(PF d L W 0)) := by
118:def BAtwistSum (d : ℕ) : Prop :=
119:  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
120:    ∀ {Ex Iy Iz : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Iy] [DecidableEq Iy] [Fintype Iz] [DecidableEq Iz]
121:      (c t' : Bool) (A : List (BAGraph Ex Iy)) (B : List (BAGraph Ex Iz)) (ℓe : Ex → Idx d L W),
122:      ∫ ω, baSum (A.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe +
123:          baSum (B.map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
124:        (if c then (star : ℂ → ℂ) else id)
125:          (∫ ω, baSum A (BAlwData d L W g0 Em t m ω) ℓe + baSum B (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))
129:theorem baTwistSum_holds (d : ℕ) : BAtwistSum d := by
209:def BAtwistFormE (d : ℕ) : Prop :=
210:  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
211:    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W)
212:      (c t' : Bool),
213:      -- (a) `lem_lweight` (`lw2`, `lw4`) at a circled self-loop
214:      (∀ p ∈ lwSplit Γ.solid, (lwSymmTwistS c t' p.1).σ = true → p.1.circ = true → p.1.src = p.1.dst →
215:        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
216:          ∫ ω, baSum (((Γ.twist c t').lw2 (lwSymmTwistP c t' p)).map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe +
217:            baSum (((Γ.twist c t').lw4 (lwSymmTwistP c t' p)).map (BAGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe
218:              ∂(PF d L W 0)) ∧
219:      -- (b) `lanlw` at a circled edge (the twisted edge is the blue out-edge of its source)
220:      (∀ p ∈ lwSplit Γ.solid, (lwSymmTwistS c t' p.1).σ = true → p.1.circ = true →
221:        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
222:          ∫ ω, baSum ((BAGraph.lanlwTerms (Γ.twist c t') (lwSymmTwistP c t' p)).map (BAGraph.twist c t'))
223:            (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) ∧
224:      -- (c) `GGGamma` (`gg2`, `gg4`) at a circled pair of one colour, an out- and an in-edge of one vertex after the twist
225:      (∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, (lwSymmTwistS c t' p.1).σ = true → p.1.circ = true →
226:        (lwSymmTwistS c t' q.1).σ = true → q.1.circ = true → (lwSymmTwistS c t' p.1).src = (lwSymmTwistS c t' q.1).dst →
227:        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
228:          ∫ ω, baSum (((Γ.twist c t').gg2 (lwSymmTwistP c t' p) (lwSymmTwistP c t' q)).map (BAGraph.twist c t'))
229:              (BAlwData d L W g0 Em t m ω) ℓe +
230:            baSum (((Γ.twist c t').gg4 (lwSymmTwistP c t' p) (lwSymmTwistP c t' q)).map (BAGraph.twist c t'))
231:              (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))
236:theorem baTwistFormE_holds (d : ℕ) : BAtwistFormE d := by
$ lake build RBM3D.Graph.BASymm2 | tail -1; lake env lean RBM3D/Graph/BASymm2.lean
Build completed successfully (3815 jobs).
exit=0 (no output above = no warning, no error)
$ lake env lean docs/tickets/checks/T2432-check.lean  (on t/T2432)
exit=0
# full build with a temporary `import RBM3D.Graph.BASymm2` after the last import of RBM3D.lean (hub step A.4), reverted afterwards
$ lake build  (output kept in the scratchpad; grep of its audit and result lines; then git status --short | wc -l)
info: RBM3D.lean:479:0: axiom audit: 12272 theorems, 3802 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4247 jobs).
exit=0
       0
$ printf 'import RBM3D\nimport RBM3D.Graph.BASymm2\n#assert_rbm_axioms\n' | lake env lean   (pre-check)
axiom audit: 12272 theorems, 3802 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded). All within [propext,  Classical.choice,  Quot.sound]; no project axioms: what the paper cites rather than proves is carri
exit=0
# #print axioms of all 30 public declarations of the file, grouped (script over `^(theorem|def)` lines; Pa, Pb, Qc, Qc_mem are instance data)
$ lake env lean axall.lean | group by axiom set
4 with [propext]: BASymm2Inst.Pa BASymm2Inst.Pb BASymm2Inst.Qc BASymm2Inst.Qc_mem
26 with [propext, Classical.choice, Quot.sound]: BAGraph.twist_invol baSum_twist baTwistIntegral_gen BAtwistSum baTwistSum_holds BASymm2_frame_mem BASymm2_pair_mem BASymm2_frame_circ 
BAtwistFormE baTwistFormE_holds ba_twist_inv_out baTwist_lanlw_ord baTwist_lanlw_scalingOrderG baTwist_lw_raw baTwist_lw_mono baTwist_lw_scalingOrderG baTwist_gg_raw baTwist_gg_mono 
baTwist_gg_scalingOrderG BASymm2Inst.G1 BASymm2Inst.G1_normal BASymm2Inst.G1_counts BASymm2Inst.Pa_mem BASymm2Inst.Pb_mem BASymm2Inst.A0 BASymm2Inst.B0
$ name-clash scan: new public names against main and the other t/T24* branches (def/theorem/lemma/abbrev/instance/structure lines); then the positive control with `baTwistIntegral_holds` appended
refs scanned: 35 names: 30 hits: 0
refs scanned: 35 names: 31 hits: 11
# compiled instances (d = 3, L = 4, W = 2, flowP_data): target 2 (484-491), target 3 (b) (508-514), the call of target 3 (c) (524-525); by `grep -n ^example`: target 1 at 477, (a) at 500, (c) statement at 518, target 4 at 534-547
$ sed -n '484,491p;508,514p;524,525p' RBM3D/Graph/BASymm2.lean
example :
    ∫ ω, baSum (A0.map (BAGraph.twist true true)) (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 +
        baSum (B0.map (BAGraph.twist true true)) (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      (if true then (star : ℂ → ℂ) else id)
        (∫ ω, baSum A0 (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 + baSum B0 (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0
          ∂(PF 3 4 2 0)) :=
  baTwistSum_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 true true A0 B0 BASymm1Inst.ℓ0

/-- **Target 3 (b)** at the red in-edge `Pb` of `x`, `(c, t') = (true, true)`: the twisted edge is the blue out-edge `G̊_{x v1}`; `lanlw` at the frame. -/
example :
    ∫ ω, G1.val (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) =
      ∫ ω, baSum ((BAGraph.lanlwTerms (G1.twist true true) (lwSymmTwistP true true Pb)).map (BAGraph.twist true true))
        (BAlwData 3 4 2 g0P EP t0P m0P ω) BASymm1Inst.ℓ0 ∂(PF 3 4 2 0) :=
  (baTwistFormE_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 G1 BASymm1Inst.ℓ0 true true).2.1
    Pb Pb_mem rfl rfl
  (baTwistFormE_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 G1 BASymm1Inst.ℓ0 true true).2.2
    Pb Pb_mem Qc Qc_mem rfl rfl rfl rfl rfl
# memberships: `SEdge` has no `DecidableEq`, so `decide` on `p ∈ lwSplit _` fails; the file uses `simp [lwSplit, ..]`
$ lake env lean inst1.lean | sed -n 1,2p   (the same membership by `decide`)
14:2: error: failed to synthesize
  Decidable
```

Narrative (every statement below is read off the output above or the file):
- Delivered in `RBM3D/Graph/BASymm2.lean` only: 554 lines against the stop line 2,000; `BASymm2B` not written (the 1a predicted < 1,700). Four section commits (450fb36, c59b4ed, 1cf089e, cf9ec0b: 143, 252, 431, 554 lines); the stop rule (CONTROL H134) never fired. `RBM3D.lean` is not edited (hub step A.4; the full build above used a temporary import line, reverted).
- Targets 2-3: the def blocks equal the check file's `T2432_TwistSum`, `T2432_FormE` up to the name (diff above); no hypothesis added, nothing weakened. The proofs of `baSum_twist`, `baTwistIntegral_gen`, `baTwistSum_holds` use neither `BASelf` nor `0 ≤ t < 1`; no integrability hypothesis anywhere.
- Target 3 proof: one private lemma `BASymm2_back` turns the frame identity at `Γ.twist c t'` into the identity at `Γ` (`baTwistIntegral_holds`, `baTwistSum_holds`); `BASymm2_back1` is its `B = []` case (`lanlw`). The frame hypotheses come from the pinned ones: `circ` by `lwSymmTwistS_circ`, the loop by `lwSymmTwistS_loop`, membership by `lwSymm_lwSplit_twistP` (`BASymm2_frame_mem`, `BASymm2_pair_mem`). The `LWSymm` band selectors are not called (the pinned hypotheses are already on the twisted edges). No `LWSymm` §4 twin needed: (a) is instanced at a self-loop at the external vertex `inl 0`, (b), (c) at the internal `x = inr 0`.
- Target 2 for L3a3: `baTwistIntegral_gen` takes any functional `F` of the data, so a 3- or 4-list macro sum is one `F`. The pathwise twist of `BAComb.val` of packed graphs is L3a3's (it needs R1's `BAPGraph.twist`); it is not in this file.
- Target 4: `ba_twist_inv_out` (counters, `scalingOrder`, `nExt`, `nLoops`, `nPairs`, `Normal`); `baTwist_lanlw_ord`, `baTwist_lw_raw`, `baTwist_lw_mono`, `baTwist_gg_raw`, `baTwist_gg_mono` hold for the twisted outputs (`list.map (BAGraph.twist c t)` of the frame lists) relative to `Γ`. The three `baTwist_*_scalingOrderG` are at the untwisted frame terms, relative to `Γ` ((d) 1; the ticket lists only `lanlw_scalingOrderG`).
- Instances: `G1` (normal `BAGraph (Fin 2) (Fin 2)` with `Ψ`- and `M`-dotted edges; `(n_S, n_W, n_A, n_M) = (4, 2, 0, 0)`, `ord = 8` by `decide`), the red self-loop `Pa`, the red in-edge `Pb` of `x`, the red pair `Pb`, `Qc`. (a) at `c = true` and every `t'`; (b), (c) at `(true, true)`; target 2 at `A0`, `B0` (two nonempty lists each, over `Fin 3` and `Fin 2`); target 1 at `G1` (also `≠`); target 4 at `Pa`, `Pb`, `Qc`. `BASelf` and `0 < t₀ < 1` are `flowP_data`; every deterministic hypothesis is discharged (`rfl`, `decide`, `simp [lwSplit, ..]`); no external hypothesis.
- Difference from (iii): `T°` commutation is proved as equality of counters and atoms (`BASymm2_circ_twist`, private), not as an equation of graphs; one private `BASymm2_mono` serves the monotonicity lemmas.
- Differences from the ticket text: memberships by `simp`, not `decide` (output above); `scalingOrderG` as in (d) 1. Ports: none (twin of the in-repo `LWSymm` §5-§6; no text from `../RBM1D` or `../RBM2D`).

## (c) Verified names (by compile)
`MeasureTheory.MeasurePreserving.integral_comp'` (Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1115); core `Init/Data/List/Lemmas.lean`: `List.map_congr_left` (:1164), `List.map_id'` (:1114), `List.mem_map_of_mem` (:1132), `List.map_map` (:1252); also `List.mem_map`, `List.map_nil`, `map_add`, `add_zero`, `Function.comp_def`. Verified absent: `DecidableEq (SEdge V)` (instance synthesis fails, (b)).

## (d) Open issues and paper-delta candidates
1. Finding for the dispatcher (as (a) "Reading"; no statement of targets 2-3 changes): target 4 of the ticket lists `lanlw_scalingOrderG` among the bounds that hold "for the twisted outputs relative to `Γ`". `scalingOrderG` is a minimum over `partition`; `scalingOrderG (T.twist c t) = scalingOrderG T` needs `LGraph.partition (twist Γ) ≅ (partition Γ).map twist`, assigned to L3b4′ (`T2423-amend-1.md` S1). Delivered: `baTwist_lanlw_scalingOrderG` for the frame terms, relative to `Γ`; `baTwist_lw_scalingOrderG`, `baTwist_gg_scalingOrderG` likewise (not listed in the ticket).
2. L3d4 (twin of `LWProv:942-1109`) needs a weighted value twist (`W : (E ⊕ I → Idx) → ℝ`); not here ((a) (v)).
3. Paper-delta candidates: none (the pinned statements are unchanged; target 4 is Lean-side bookkeeping). Section (a) needed no correction, so there is no (a′).
