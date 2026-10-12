Auditor model: claude-opus-5-5

# T2432 audit, round 1 (Rule (H) rerun; written Mon Oct 12 03:13:35 UTC 2026)

Branch `t/T2432` at `cf9ec0b` (main `35279ca`); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2432-audit2` (detached at cf9ec0b, fresh).
Sole writable files: `RBM3D/Graph/BASymm2.lean`, `RBM3D/Graph/BASymm2B.lean` (unused), `RBM3D.lean` (import lines; left to the hub, A.4).

## 1. Build, diff, hygiene

```
$ lake build RBM3D.Graph.BASymm2 | tail -1        (audit worktree)
Build completed successfully (3815 jobs).
$ lake env lean RBM3D/Graph/BASymm2.lean 2>&1 | grep -cE "warning|error"
0
$ git diff --name-status main...t/T2432
A	RBM3D/Graph/BASymm2.lean
$ grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom ' RBM3D/Graph/BASymm2.lean || echo none
none
$ lake env lean docs/tickets/checks/T2432-check.lean >/dev/null; echo "check exit=$?"     (on t/T2432)
check exit=0
```

```
$ lake env lean ax.lean     (#print axioms of every public theorem of the file)
'RBM.Graph.BAGraph.twist_invol' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baSum_twist' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwistIntegral_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwistSum_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwistFormE_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.ba_twist_inv_out' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_lanlw_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_lanlw_scalingOrderG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_lw_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_lw_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_lw_scalingOrderG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_gg_raw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_gg_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.baTwist_gg_scalingOrderG' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```
$ name clash: new public decl names on main (git grep "(theorem|def|lemma|abbrev|namespace) <name>")
twist_invol:0 baSum_twist:0 baTwistIntegral_gen:0 BAtwistSum:0 baTwistSum_holds:0 BAtwistFormE:0 baTwistFormE_holds:0
ba_twist_inv_out:0 baTwist_lanlw_ord:0 baTwist_lanlw_scalingOrderG:0 baTwist_lw_raw:0 baTwist_lw_mono:0 baTwist_lw_scalingOrderG:0
baTwist_gg_raw:0 baTwist_gg_mono:0 baTwist_gg_scalingOrderG:0 BASymm2_frame_mem:0 BASymm2_pair_mem:0 BASymm2_frame_circ:0 BASymm2Inst:0
$ same regex on t/T2423, t/T2433:   t/T2423: 0   t/T2433: 0
```
Line count 554 (stop line 2,000); `BASymm2B` not written.

## 2. Statements against the pins (targets 2, 3)

```
$ python3 ext.py docs/tickets/checks/T2432-check.lean RBM3D/Graph/BASymm2.lean
  (def block from `def <name> ` to the first blank/docstring line, name replaced by NAME, string compare)
== T2432_TwistSum (8 lines) vs BAtwistSum (8 lines): IDENTICAL
== T2432_FormE (23 lines) vs BAtwistFormE (23 lines): IDENTICAL
```
`baTwistSum_holds (d) : BAtwistSum d` (:129) and `baTwistFormE_holds (d) : BAtwistFormE d` (:236): for every `d`, no extra hypothesis.
Target 1 `BAGraph.twist_invol (c t) (Γ) : (Γ.twist c t).twist c t = Γ` (:69): as the ticket.
Pathwise list form `baSum_twist` (:87): hypotheses `hS`, `hP` (real `S`, `gPsi`) are discharged at the BA data by the merged
`BASymm1_data_real` inside `baTwistSum_holds` (:135); same form as its twin `BASymm1_val_twist`. `baTwistIntegral_gen` (:104) has no
integrability hypothesis and an arbitrary `F : BALData (Idx d L W) → ℂ`; this is how L3a3's 3- and 4-list sums are transported (ticket target 2, last sentence).

## 3. Vacuity, hidden hypotheses, cycles

- No structure with Prop fields is introduced; `BAtwistSum`, `BAtwistFormE` are `Prop` defs with all hypotheses explicit.
- Hypotheses of (a)–(c) are on the twisted edge (`(lwSymmTwistS c t' p.1).σ = true`, `p.1.circ`, loop / `src = dst` of the twisted pair), exactly as pinned;
  they are passed to the merged `baExpFrame_lw` (BAWeightOp), `lanlw_val` (BAExpandW:908), `baExpFrame_gg` (BAGGOp) at the frame `Γ.twist c t'`
  via `BASymm2_frame_mem`, `BASymm2_pair_mem`, `BASymm2_frame_circ`, `lwSymmTwistS_loop` (:240-248). Back-transport `BASymm2_back` uses merged
  `baTwistIntegral_holds` (BASymm1) and `baTwistSum_holds` (this file). Dependencies are merged modules only (imports :6-10); no cycle.
- C1: only `BASelf`, `3 ≤ L`, `0 ≤ t < 1`; no `M a b = 0`, `M a a = m`, uncircling, or smallness of `g0` (signatures :119, :210).
- External hypothesis: none.

## 4. Compiled nonempty instances (`d = 3`, `L = 4`, `W = 2`, `flowP_data` from `BA/CouplingWindow.lean:869`)

```
$ grep -n '^example' RBM3D/Graph/BASymm2.lean
477 (target 1, plus G1.twist true true ≠ G1)   484 (target 2, A0, B0)   493 (baTwistIntegral_gen, nonlinear F)
500 (3a, Pa, c=true, any t')   509 (3b, Pb, (true,true))   518 (3c, Pb, Qc, (true,true))
528 (frame lists nonempty: lanlw 4, lw2 4, gg2 7 terms, by rfl)   534-542 (target 4, nine lemmas)   545 (ord = 9 at lanlw terms)
```
- `G1 : BAGraph (Fin 2) (Fin 2)` (:439): 4 circled solid edges (red self-loop, red in-edge of `x`, red out-edge of `x`, one blue), 2 waved,
  1 `×`-dotted, one `Ψ`-edge, one `M`-edge, coeff `1 + i/2`; `G1_normal` and `G1_counts` (ord = 8) by `decide`.
- Every deterministic hypothesis is discharged: `3 ≤ 4` by `norm_num`; `BASelf`, `0 ≤ t0P`, `t0P < 1` by `flowP_data`; memberships
  `Pa_mem`, `Pb_mem`, `Qc_mem` by `simp [lwSplit, ..]` (:468-470); σ, circ, loop, `src = dst` by `rfl`. No hypothesis left open.
- Target 2 at `A0` (2 graphs over `Fin 2, Fin 3`) and `B0` (2 graphs over `Fin 2, Fin 2`), `(c, t') = (true, true)`.
- Ticket target 5 asks `c = true` in (a)–(c), `t' = true` in (b), (c): met. Nondegenerate: `N = 512`, nonempty lists, nonempty frame outputs (:528).

## 5. Target-by-target verdict

| target | verdict | evidence |
|---|---|---|
| 1 `BAGraph.twist_invol` | PASS | §2, instance :477 |
| 2 `BAtwistSum` / `baTwistSum_holds`, `baSum_twist`, `baTwistIntegral_gen` | PASS | pin IDENTICAL, no integrability hypothesis, instances :484, :493 |
| 3 `BAtwistFormE` / `baTwistFormE_holds` | PASS | pin IDENTICAL, instances :500, :509, :518 |
| 4 invariants of twisted outputs | PASS (see Observation O1) | `ba_twist_inv_out` (counters, scalingOrder, nExt, nLoops, nPairs, Normal), `baTwist_lanlw_ord`, `baTwist_lw_raw/_mono`, `baTwist_gg_raw/_mono` for `.map (BAGraph.twist c t)` relative to `Γ`; instances :534-547 |
| 5 instances | PASS | §4 |
| 6 C1, registry | PASS | §3; no registry line |

## 6. Paper deltas

No Lean/paper statement difference is introduced: targets 2–3 are the Lean transport of the merged frame identities (`lanlw`, `lem_lweight`,
`GGGamma`, `B_graphical_lemmas.tex:353-405`) under the twist; target 4 is Lean bookkeeping. The prove report proposes none; none needed.

## 7. Observations (no statement, instance, build, axiom or paper-delta effect)

- **O1 (for the dispatcher's record).** Ticket target 4 says `lanlw_scalingOrderG` "holds for the twisted outputs relative to `Γ`".
  Delivered `baTwist_lanlw_scalingOrderG` (:321) and the unrequested `baTwist_lw_scalingOrderG`, `baTwist_gg_scalingOrderG` are stated at the
  **frame terms** (untwisted), relative to `Γ`. `scalingOrderG` is a min over `BAGraph.partition = splitG.map packMerge` (BAVocab:229-236), whose
  terms live on `ExtCls`/`IntCls` of the graph, so it is not a consequence of the counters; the bridge `LGraph.partition (twist Γ) ≅ (partition Γ).map twist`
  is assigned to L3b4′ by `docs/tickets/T2423-amend-1.md:3` (S1). The design consumer `BAstepMono` (T2395-design:78, 86) works at the frame step, where the
  delivered form applies. The ticket's "Hence" is not derivable from the listed invariants; the deviation is recorded in prove report (d) 1. Not a RETURN.
- O2. Public helpers `baSum_twist`, `baTwistIntegral_gen`, `ba_twist_inv_out`, `baTwist_*` are named in the 1a section map ((a)(iii)) as target
  declarations; `BASymm2_frame_mem/_pair_mem/_frame_circ` carry the stem (§3 (E) satisfied).
- O3. Memberships by `simp`, not `decide` (ticket target 5): `SEdge` has no `DecidableEq`; the hypothesis is still discharged at concrete data.

## Verdict

**T2432: PASS** (all targets). No dispatcher sign-off required; O1 is recorded for the dispatcher's L3b4′ bookkeeping.
