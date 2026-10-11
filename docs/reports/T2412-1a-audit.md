Auditor model: claude-opus-5-5

# T2412 1a-audit (design gate) — Sun Oct 11 08:25:10 UTC 2026

Inputs: ticket `docs/tickets/T2412.md`; `docs/reports/T2412-prove.md` sections (a), (a″); branch `t/T2412` at `668318f`.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2412-1a-audit1` (detached at `668318f`). Scratch: `$S` = `<scratchpad>/T2412` (CONTROL H28). `aud_*` files are mine; the other files are the prover's.

**Verdict: PASS** (every item (i)–(v) is met, no binding stop line is hit, the atom step closes so no REQ is needed). Observations O1–O5 below; O1 is a binding direction for stage 1b and repeats the ticket's own R/reuse rule.

## 1. Probe: compile, axioms, hygiene, diff scope

```
$ git log -1 --format="%h %s"; git diff --stat main...HEAD; wc -l RBM3D/Probe/T2412Pins.lean
668318f T2412: probe, example also applies the T2 counters/forest pins at baLWT1
 RBM3D/Probe/T2412Pins.lean | 303 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 303 insertions(+)
     303 RBM3D/Probe/T2412Pins.lean
$ git diff --stat 3dbc25f main -- RBM3D/        # main has not moved under RBM3D/ since the branch base
(empty)
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/Probe/T2412Pins.lean; echo "grep exit=$?"
grep exit=1
$ grep -n "T2412Pins\|Probe" RBM3D.lean; echo "exit=$?"            # no root import
exit=1
$ lake env lean RBM3D/Probe/T2412Pins.lean > $S/aud_probe.txt; grep -nE "error|warning|exit=" $S/aud_probe.txt
37:exit=0
$ # scratch copy: example renamed to a theorem + three #print axioms lines
$ diff RBM3D/Probe/T2412Pins.lean $S/aud_ax.lean
247c247
< example (hEq : baSp_eq_pin) (hDec : baSpDecay_pin) (hKB : baKBound_E_pin) (hSz : baClaimSize_pin)
---
> theorem aud_T2412_inst (hEq : baSp_eq_pin) (hDec : baSpDecay_pin) (hKB : baKBound_E_pin) (hSz : baClaimSize_pin)
302a303,305
> #print axioms RBM.Graph.aud_T2412_inst
> #print axioms RBM.Graph.T2412Inst.D0
> #print axioms RBM.Graph.BAGraph.sizeConst
$ lake env lean $S/aud_ax.lean 2>&1 | grep -E "depends on|error|sorry"
'RBM.Graph.aud_T2412_inst' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.T2412Inst.D0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAGraph.sizeConst' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
The probe has 303 lines (limit 400) and compiles with exit 0 and only the standard axioms. It is the only file in the diff.

## 2. Reruns of the prover's numerics (section (a)(ii))

```
$ cd $S && python3 counters.py && python3 report.py && python3 wscan1.py && python3 cone.py <wt> RBM3D.Graph.BAVocab RBM3D.Graph.LWSizeClaim
baGGT1 {'nS': 0, 'nW': 1, 'nA': 1, 'nM': 0, 'nV': 3, 'waved_tree': 1, 'dotted_tree': 2}
baLWT1 {'nS': 2, 'nW': 1, 'nA': 2, 'nM': 1, 'nV': 3, 'waved_tree': 1, 'dotted_tree': 1}
g=0.01562 Lam=0.01562 kappa=0.9993 cM=0.5 mu=1.93e-09 KM=1.98e+05 K0=4.24e+12 K1=1.87e+51 | actual maxM=0.999 rowM=1.101 rowSp=0.334 max|Sp|W^d e^(mu dB)=0.333
    G1=baGGT1 |val|=0.0103 <= K1*Kd^4*1=2.86e+72;  G2=baLWT1 |val|=0.0255 <= K1*Kd*size=1.89e+55 (size=0.0512, |val|/size=0.498)
g=1 Lam=1 kappa=0.5959 cM=0.0485 mu=2.17e-22 KM=2.3e+10 K0=5.02e+21 K1=1.38e+112 | actual maxM=0.596 rowM=5.822 rowSp=0.525 max|Sp|W^d e^(mu dB)=0.429
    G1=baGGT1 |val|=0.00617 <= K1*Kd^4*1=3.85e+153;  G2=baLWT1 |val|=0.00425 <= K1*Kd*size=1.62e+121 (size=0.0512, |val|/size=0.0829)
g=10 Lam=10 kappa=0.5594 cM=0.00465 mu=8.66e-32 KM=2.82e+15 K0=6.94e+29 K1=7.59e+157 | actual maxM=0.559 rowM=4.652 rowSp=0.548 max|Sp|W^d e^(mu dB)=0.441
    G1=baGGT1 |val|=8.04e-06 <= K1*Kd^4*1=4.83e+219;  G2=baLWT1 |val|=0.000427 <= K1*Kd*size=1.1e+172 (size=0.0512, |val|/size=0.00833)
g=0.01562 Lam=10 kappa=0.9993 cM=0.00829 mu=1.64e-27 KM=1.57e+14 K0=2.04e+25 K1=1.73e+136 | actual maxM=0.999 rowM=1.101 rowSp=0.334 max|Sp|W^d e^(mu dB)=0.333
    G1=baGGT1 |val|=0.0103 <= K1*Kd^4*1=1.04e+193;  G2=baLWT1 |val|=0.0255 <= K1*Kd*size=1.39e+149 (size=0.0512, |val|/size=0.498)
tail threshold: log W0=(2D/c)^(1/eps1), D=3, eps1=1/20, c=cM(g=1,Lam=1,kappa=0.5959)=0.04846: log W0=7.15e+41
W=1 g=1: |G1|/size1=0.0061714 |G2|/size2=0.082925
W=2 g=1: |G1|/size1=0.0061714 |G2|/size2=0.082925
W=3 g=1: |G1|/size1=0.0061714 |G2|/size2=0.082925
RBM3D.Graph.BAVocab 3 modules; LWExpCert in cone: []
['RBM3D.Graph.BAVocab', 'RBM3D.Graph.LWVocab', 'RBM3D.Graph.ScalingOrder']
RBM3D.Graph.LWSizeClaim 48 modules; LWExpCert in cone: []
```
These outputs match (a) lines 68-82 digit for digit. `inst.py:28,35` asserts the Ward row and `S⁺ = t·W^{-d}Θ_{[x][y]}` inside `run`, which `report.py` calls at every point, and both asserts pass. I checked the script's constants against the Lean definitions: `BAct_rate` (`BA/CombesThomas.lean:45`), `BAct_C` (`:42`), `BAp5s_A/_rate/_C` (`BA/Prop5Short.lean:49-60`) and `expC` (`Defs/RadialSum.lean:271-272`) all match `inst.py:15-22`.

Union cone of the five planned imports (this line in (a) has no command; O4):
```
$ python3 -I $S/aud_cone_union.py $S/cone.py <wt> RBM3D.Graph.LWSizeClaim RBM3D.Graph.BAVocab RBM3D.Graph.BAExpandW RBM3D.BA.GreenSchur RBM3D.BA.Prop5Short
99 modules in the union cone; LWExpCert: [] ; Probe: []
```

## 3. Independent check of the pinned bound (T3) at the actual constants

The prover's checks use the Lean constants. Those are about 10^50 or larger, so the checks cannot fail. I therefore brute-forced the pinned inequality `|val| ≤ ‖coeff‖·N^{n_M}·K₁^{n_A−n_M}·a^{n_W−(n_A−n_M)}·Kd^{#M+#Ψ}·Ψ^{n_S}` (this is `sizeConst·scalingSize` with `a = K₀W^{-d}` and `N = (WL)^d`) with the **actual** constants: `a` = largest entry of `S` and `S⁺`, `K₁` = largest row or column sum, `Kd` = largest entry, row sum or column sum of `M` and `gΨ`, and `|G−M| ≤ Ψ = 1`. The test uses random normal BA graphs with all solid edges circled, no `=`-dotted edge, waved edges of types `S`, `S⁺` and `S⁻ = (S⁺_{yx})*`, `M`/`M̄`-dotted, `Ψ`-dotted and `×`-dotted edges, and 0–2 external vertices. Half of the cases use flat `S = J/n`, which is the sharp regime `N·a = K₁`.
```
$ python3 $S/aud_claim_rand.py
3000 random BA graphs (normal: all solid circled, no =-dotted), max |val|/bound = 1.000000
```
There were no violations, and the counter inequalities `n_M ≤ n_A` and `n_A − n_M ≤ n_W` (the `BAGraph_counters_le_pin`) held in every case. The ratio reaches 1, so the bound is attained (it is sharp, not slack).

## 4. Design-gate items

| item | finding | status |
|---|---|---|
| (i) atoms | A2: atoms are the `{M,Ψ}`-dotted components and molecules the `{waved,M,Ψ}` components. These agree with `BAGraph.atomAdj`/`adj` (`BAVocab.lean:96-131`) under `Normal` (no `=`-dotted edge); `×`-dotted edges join neither (`LGraph.adj`, `LWVocab.lean:157-159`). Counting: non-target atoms are the internal atoms that are not molecule roots, `n_A − n_M` of them, each with one waved gate edge. The dotted spanning trees inside atoms give `n_V − n_A` edges, so `|C| = n_V − n_M`. Gate edges are pairwise distinct because the ranks strictly decrease along them. The rank `ρ = rk·(|I|+1) + depth` is monotone across the gate. I re-derived this and it is correct. A3 peels per edge and gives `W^{-d(n_W−n_A)}(L^d)^{n_M}`, which is `scalingSize` (`BAVocab.lean:161-165`, `(eq_defsize_BA)` at `B:345-350`). The uniform rate enters only through `K_M`, `K₀` and `K₁` (rates `c`, `μ` fixed by `(d,Λ,κ)`). No hypothesis of the form `g ≤ W^{-ε}`, no smallness of `‖M−m₀‖` and no `(Cλ)^{|a−b|}` term appears in any pin (L5); I read all 13 pins. | met |
| (ii) kernel edges | `S⁺ = SW = t·lwLift(Θ⁺⁺)`. Here `(M⁺S)_{xy} = tW^{-d}(M^B∘M^B)_{[x][y]}`, because `M` is offset-diagonal (`BAMres_fine_apply`) and `lwLift` contains the `W^{-d}` (`LWSizeClaim.lean:87-88`). `Θ = PropThetaQ(BAMss …)` (`MFixedPoint.lean:515`). `BAProp5s` bounds only `Θ(0,a)` (`FlowPins.lean:190`), so the translation shift (A4) is needed. The bound `(1+Λ²)C₅e^{-μ d_B}` follows. The pin `baSpDecay_pin` has `∃ C c` ahead of `∀ L W g0 E t m`, so its constants are uniform. The numerics confirm `S⁺ = tW^{-d}Θ` (assert). | met |
| (iii) statement | `baClaimSize_pin` takes `Normal`, `‖G−M‖ ≤ Ψ` entrywise, and `LWKBound` for `S`, `S⁺`, `M` and `gΨ`; it has no `hM`. A circled solid edge evaluates to `G−M` (`SEdge.val`, `LWVocab.lean:115-117`), and `Normal` forces every solid edge to be circled (`BAVocab.lean:170-171`), so the hypothesis is exactly the one the bound uses. Unlike the band's `hG`/`hGd` split, no `ℓ x ≠ ℓ y` case split is needed. `BALData` has no `Prop` field (`BAVocab.lean:31-32`), so nothing is hidden. The general form goes through `BAGraph.partition` (`Σ_P C_P · max size`, mirroring `lwClaimSizeG`). | met |
| (iv) constants | Checked at `g = 1/64, 1, 10` with `κ = Im m` from the self-consistent `m`, plus a fourth point `(g, Λ) = (1/64, 10)`; rerun above. The probe point `P : FlowPt 4 10` serves only as an instance. | met |
| (v) pins/split | The 13 pins are compiled as `Prop`s, and one `example` applies 12 of them at `d=3, L=4, W=2, t=1/2, P`: `Normal` is discharged by `decide`, `hG` by `simp`, and `0 < size` by `norm_num`. The remaining hypotheses are the ticket's own targets, as a probe allows. The file plan splits by section: `BASizeClaim` = T1+T2, `BASizeClaim2` = T3+T4+instances. Merge cone: 3 or 99 modules, with no `LWExpCert` and no `Probe` module. | met (O2, O3) |
| stop lines | Per-file limit 2,000 lines: two files are planned (sizes in O2). Atom step: it closes, so no REQ. | not hit |

Paper-delta coverage: `T2412a` (Combes–Thomas for all `g₀ ≤ Λ`), `T2412b` (no `(log W)^{1+ε₁}` atom-spread loss) and `T2412c` (`S⁺ = SW`) are proposed. The deterministic form and the `ℓ¹-L¹` peeling are the band's D265/D266, the block distance `d_B` is D268, the reading of atoms is D599 (T2287a–b), and the absence of a paper proof is D101 (T2040m), all already in `docs/paper-deltas.md` (lines 417, 1071-1083, 1558). Every Lean/paper difference in the pins is covered.

Planned public names have no clashes:
```
$ for n in <15 planned names>; do grep -rnE "(theorem|def|lemma|abbrev) $n( |$)" RBM3D | grep -v Probe/ | wc -l; done
baSp_eq:0 baSpDecay:0 baKBound_E:0 BAGraph.exists_forest:0 BAGraph.counters_le:0 baClaimSize:0 baClaimSizeG:0 baClaimSize_E:0 baClaimSizeG_E:0 baSpTail_E:0 baMTail_E:0 baTail_log:0 BAGraph.sizeConst:0 BAGraph.Jx:0 BAGraph.edgeEnds:0
```

## 5. Observations (no change to any pin, instance, build, axiom or delta coverage)

- **O1 (reuse; binding direction for 1b, answering (a″) item 4).** The ticket's R line says "`LWSizeClaim` §1, §4, §5 … Reuse them; do not twin them." A3 instead plans to twin the private `lwForest_core` (`LWSizeClaim.lean:544`), on the grounds that `lwForest_sum_le` "does not suffice". In fact the per-edge pin `BASizeClaim_forest_sum_le_pin` follows from the public `lwForest_sum_le` (`:637`) in three steps:
  1. Bound pointwise: `∏_j f_j ≤ ∏_{c∈C} f_{e(c)} · ∏_{j∉e(C)} a_j`, using `0 ≤ f ≤ a` and `InjOn edge C`.
  2. Apply `lwForest_sum_le` with `J' := {c // c ∈ C}`, `f'_c := f_{e(c)}/K_{e(c)}`, `K' = 1`, `edge' = id`, and any `a' ≥ 0`. Since `|J'| − |C| = 0`, the `a'` power is 1.
  3. Handle `K_{e(c)} = 0` separately: then row sums are 0 and `f ≥ 0` force `f_{e(c)} ≡ 0`, so both sides vanish.

  Stage 1b keeps the pin as written and proves it through this reduction, without copying `lwForest_core`. `BAGraph.exists_forest` is a new construction (the atom clause has no band counterpart; ticket (i)); it may copy the private `lwExists_rank` under the `BASizeClaim_` stem.
- **O2 (file plan numbers).** (a) says "Central estimate above 1,500" but gives no per-file numbers. I sized the band file by section:
  ```
  $ grep -n "^/-! ## " RBM3D/Graph/LWSizeClaim.lean | awk …   (1484 lines total)
  §1 45 · §2 83 · §3 284 · §4 188 · §5 143 · §6 363 · §7 55 · §8 140 · §9 105
  ```
  The band counterpart of file 1 (§2-5) is 698 lines and of file 2 (§6-9) is 663 lines. At twice the band size each file would be about 1,400 lines, under the 2,000 stop line. The 1b report must open with the actual counts (ticket).
- **O3 (instance labels).** (a) T5 says `a0` and `a1` must share an offset, yet the probe's `baGGT1` labels `![fun _ => 0, fun _ => 1]` have different offsets at `W = 2` (`split`, `Defs/Sizes.lean:64`). That `baGGT1` value is therefore identically 0. This does not make the instance degenerate: the data is nondegenerate, and the `baLWT1` application has value about 0.0255 at `g = 1/64` (§2). Stage 1b's `baGGT1` instance should use labels with the same offset in distinct blocks, for example `fun _ => 0` and `fun _ => 2`.
- **O4 (report fidelity).** (a) line 83 ("union cone of the five planned imports: 99 modules") is not produced by the command printed at line 67. I reproduced it in §2 (99).
- **O5 (constants).** `K₁` runs from about 10^51 to 10^158, because `μ = BAp5s_rate` is about 10^-9 to 10^-31. These are hard-coded constants (CLAUDE.md §7), not witnesses of a hypothesis, and the exponents of `size` do not depend on them. The `W₀` of `baTail_log` (`log W₀ ≈ 7e41`) appears only inside an existential conclusion and is not used by T3.

## 6. Verdict

- T1 kernel edges: PASS. T2 atom peeling and forest: PASS (with O1 binding the proof route). T3 `baClaimSize`/`baClaimSizeG`: PASS. T4 model form and tails: PASS. T5 instance plan: PASS (O3).
- **1a-audit: PASS.** No dispatcher sign-off is needed: O1 enforces the ticket's own rule, and stage 1b may start.
