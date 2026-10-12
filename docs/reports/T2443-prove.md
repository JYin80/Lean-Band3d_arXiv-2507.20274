Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 06:42:00 UTC 2026

Scope: mathematics of targets 1-8 and the ticket's design-gate items 1a (i)-(v). Evidence: files at `../RBM3D-wt/T2443` (= main c43bdf1 plus nothing), the ticket, the check file, and the script below.

### (i) Exponent / constant table

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | thresholds of (6) | `all`: `2p`; `far`: `3p`; instance `p = 2`: 4 and 6 | start terms `BAInit p` (merged, `BAScost:582`) | script: start min cost 4 (all) and 6 or vacuous (far): slack 0 at p = 2 |
| 2 | cost level `k` along a step | unchanged: `locCostGeA far k P → locCostGeA far k Q` | `locCostGe_locStep` (6d:1077) keeps the same `k`; `P'.g.Normal`, `CircIffLoop P'.g` as hypotheses (6d:1077-1079) | exact, no loss |
| 3 | final step | `k ≤ ord` and, far, `k ≤ ord` | the trivial merge costs `ord` at `LocStd` (`locReg6_of_locCostGe`, `locReg6far_of_locCostGe`, 6a:645, 653) | script (LocStd graph L): `ord = cost(⊥) = 8`, `2p = 4` slack 4, `3p = 6` slack 2 |
| 4 | twist (target 3) | `scostA (P.twist c t) s = scostA P s` for `s ≥ atoms` | equality, no loss | 0 (identity); script: 15 of 15 setoids |
| 5 | bridge (target 2) | `scostA P (comap vmap s') = scost P.img.g s'` | equality, no loss | 0; script: 15 of 15 setoids at `P_B` and its twist |
| 6 | `BAEquivC` transfer | `scost (R.relabel (Sum.map eE eI)) = scost S` | `scost_perm` needs `solid.Perm`, equal `waved.length` | 0; both from `BAEquivC` fields (`BASim:234-243`) |
| 7 | cutoff `K` of `BAReach K` | free in `ℤ` | not used by the cost estimates | no constraint |

Route per design-gate item (math only; names are files' own):

**1a (i) `BAMatchTw`: dropped.** Consumers: `git grep BAMatchTw` on main, `t/T2433`-`t/T2435`, `t/T2441`, `t/T2442`, `t/T2443` finds only docstrings (`BASim.lean:16`, `BALvl1A.lean:42`); no `.lean` declaration and no ticket target uses it (T2442 ticket line 16: "Not here"). `BASimC'` asks only `∃ P'`; `P' := (P.twist c t).img`. Target 3 holds (below), so the route stands and the three bridges are not needed.

**Target 3 (twist)** holds. `atomSetoid (Γ.twist c t) = atomSetoid Γ` (`BAGraph.BASymm1_twist_atom`, `BASymm1:101`; `Setoid.ker`). `promoteC (Γ.twist c t)` and `lwSymmTwistG c t (promoteC Γ)` have the same solid list (the twist keeps `circ` and swaps ends, `e.circ && decide (atomSetoid .. src dst)` is symmetric in the ends) and the same `waved.length`; so `localReg6a_scost_congr` (6a:426) then `LGraph.scost_twist` (6d:172) give `scostA (twist Γ) s = scostA Γ s`. `BAPGraph.twist` changes only `g` (`BASim:249`), so `E'`, `I'`, `ext` and the side condition `atomSetoid ≤ s` do not move.

**Target 2 (ii) bridge.** `P.img = lvl1Comp (promoteC P.g).mergeP P.ext _` (`BAAtomic:111`), `.g = (promoteC P.g).merge`, `.ext = extMap ∘ P.ext`. `vmap : E'⊕I' → ExtCls⊕IntCls` is onto, `vmap (inl a) = inl (extMap a)` (`BAAtomic:202`), `ker vmap = atomSetoid` (`BAAtomic:226`). (⇐ at `s'`): `s := comap vmap s' ≥ atoms`; the far clause is `s' (inl (extMap (P.ext 0))) ..`; `scostA P.g s = (promoteC P.g).scost (comap vmap s') = (promoteC P.g).merge.scost s'` by `scost_relabel` (6a:401) and `localReg6a_scost_congr` (the merge differs from `relabel vmap` only in `dotted`, unread by `scost`; the pattern is the `e1` step of `BAScostLL_of_band`, `BAScost:649`). (⇒ at `s ≥ atoms`): `s' := comap (surjInv vmap) s`, and `comap vmap s' = s` because `ker vmap ≤ s` (as `BAScostLL_of_band`, `hcomap`). No `CircIffLoop`, no normality used. **`BAEquivC` transfer** (`T2443_EquivCost`): `vm := Sum.map eE eI` is an equivalence, `scost_relabel` at `vm` then `scost_perm`; the far clause moves by `S.ext a = eE (R.ext a)`; both directions by `comap vm` and `comap vm.symm`.

**1a (iii) final step.** No half-edge table is needed: for `P.g.LocStd`, `P.g.Normal` is its first conjunct; `BAGraph.img_locStd_iff` (`BAAtomic:661`) gives `P.img.g.LocStd`; `locReg6_of_locCostGe` already contains `nElem_eq_zero_of_locStd` (6a:645); `P.img.g.scalingOrder = ord P.img.g.counters = ord P.g.counters = P.scalingOrder` by `BAImgCounters_holds` (`BAAtomic:710`). Bridge turns `locCostGeA false k P` into `P.img.LocCostGe false k`. Far: the new lemma "distinct external atoms give distinct externals of `P.img`" is 4 lines: `¬ atomSetoid (inl (P.ext 0)) (inl (P.ext 1))` is `sameAtom = false` (`BAAtomic_atomSetoid_iff`, `BAGraph.BAAtomic_sameAtom_iff`), then `BAScost_vmap_ne_of_sameAtom` (`BAScost:816`, public) and `BAAtomic_vmap_inl` give `extMap (P.ext 0) ≠ extMap (P.ext 1)`; `locReg6far_of_locCostGe` applies. The route is hence not through the vertex-level `locStdA`.

**Target 4 (`BASimC'`)** at `T = BALocStepT`: given `P`, `c`, `t`, `LT0` with `BAFrameStepT P2 LT0`, `P2 := P.twist c t`, `P2.g.Normal` (`ba_twist_inv_out`, `BASymm2:258`, and `P.g.Normal`). `P' := P2.img`: normal and `CircIffLoop` by `BAGraph.img_normal` (`BAAtomic:308`). Cost half: `locCostGeA far k P → locCostGeA far k P2` (target 3) `→ P2.img.LocCostGe` (target 2). For `(band, Q) ∈ LT`: `Q = twist c t Q0` with `(band, Q0) ∈ LT0`; `baMatch_holds m` (`BASim3:218`) at `P2` gives `L'` with `LocStep m P2.img L'` and `R ∈ L'`, `R.BAEquiv Q0.img`; `BASim_BAEquiv_toC` (`BASim:245`), target 2 (EquivCost), bridge at `Q0`, target 3 at `Q0` give `R.LocCostGe far k → locCostGeA far k Q`. The `∃ L'` is per output, so the `gg` case (two selectors) is covered. No band step at `P.img` itself.

**Targets 1, 5, 7: normality is automatic (finding).** Every output of every `BAFrameStepT` constructor is `P.outsT tg Ts` or a concatenation of these, so its `g` is the `g` of an element of `T.partition`; `BAGraph.partition_normal` (`BAVocab:930`) has no hypothesis. Hence `BANormal (untag BALocStepT)` holds with no frame-normality hypothesis (twist back by `ba_twist_inv_out`), and the frame-normality hypothesis of `T2443_LocReg6` can be discharged here. The probe fixes the text; I propose to drop it (a stronger theorem) and report the change.

**Target 5 shapes.** `BAShape.s1` never occurs as a tag: `tagStd` gives `e2`/`band`, `tagT1` gives `e1`/`band`, the others are constants `macroA`/`macroB` (`BASim:113-136`); `grep -n "\.s1" BASim.lean` finds no occurrence; so `BAShapeLL s1 BAFrameStepTN` is vacuous. `e1` occurs only through `P.outsT P.g.tagT1 [lanlwT1 P.g p]` in `edge` and `ggSplit`, with `hp`, `h` from the constructor; its output equals `BAScost_pack P Q0` for `Q0 ∈ (lanlwT1 P.g p).partition` (`outsT` unfolds to `packMerge` of `splitG`), which is the hypothesis of `baShapeLL_e1` (`BAScost2:82`).

**Target 7.** `ba_ord_ge_of_simC'` = `baStep_of_simC'` + the induction of probe 95 (`ba_ord_ge`, `t/T2397:RBM3D/Probe/T2397Pins.lean`) via `BReach.ind` (`BAScost:105`); `BAReach K P0 Q → Q.g.Normal ∧ BReach (untag BALocStepT) P0 Q` by induction on `BAReach` (the step gives `BALocStep Q L`; `untag` iff of target 1 gives `BALocStepT` once `Q.g.Normal`; `R ∈ L` is normal by the finding above; `P0` normal by `partition_normal`).

**Premise scan** (`Test/Axioms.lean:390-445`: a `Prop` def in a theorem binder needs a public theorem concluding it). `grep` of conclusions `untag`, `BANormal`, `locReg6InvA`, `BAFinal`, `BAStep` over `RBM3D/` finds none. Provers to add (all `theorem`): `untag BALocStepT P (..)` from `BAFrameStepT (P.twist c t) LT0` (already concluded by `hTA`-`hTE`, `BASim3:1895-1903`) and `P.g.Normal` (`normalB`, `normalC`, `BALvl1A:649-650`); `BANormal (untag BALocStepT)`; `locReg6InvA p P0` for `P0 ∈ (ofLGraph (fxyPowGraph p)).partition` (from `baInit_holds`); `BASimC' m BALocStepT`; `BAFinalS R`; `BAStep (untag BALocStepT)`. `BTStep`-valued defs (`BALocStepT`, `BAFrameStepTN`) have type `BTStep`, not `∀ .., Prop` syntactically, so they are not scanned; a binder `P.g.LocStd` needs a theorem concluding `BAGraph.LocStd` (the instance at the LocStd graph gives it). To be confirmed by `import RBM3D` + `#assert_rbm_axioms` in the probe.

**1a (iv) T2426 O2, priced.** `BAScostLL P.g X` is needed for every builder term `X` that can carry `e2` (`tagStd`) or `macroB` stage 1: `lanlwD` (1), `lw2` head (1), `lw4` head and tail (2), `within` head (1), `gg2` heads 2-5 (4; head 1 is `BAGGOp_A1`, covered by `BAScostLL_S1`) and tail (1), `gg4` heads (2) and tail (1), `ggSplit` `d1` (1), `d2`, `d3`, `d4` (3): 17 new shapes (`BAWeightOp:68-80`, `BAGGOp:73-96`, `BAExpandW:133`, `BASim:113-136`). Analogs in `BAScost.lean` measured by script: `BAScostLL_S1` 68 lines, `macroA` 75, `lanlwT1` 79, `macroB` 53; shape tools 120 (§7) and 136 (§9-10) lines for one fresh vertex; `lw4`, `gg4` need a four-vertex map. The two stage-2 implications need the band step at a transfer graph (`BAFrameStepT.weight`/`gg` hypotheses at `tr`, `baMatch_holds` at `tr`). Estimate `17 × 53..79 ≥ 900`, plus tools `≥ 130`, plus stage 2 `≥ 150`: about 1,200-1,600 lines, far above 400. **Decision proposed: O2 stays hypotheses** (`BAShapeLL sh BAFrameStepTN` for `sh ∈ {e2, macroA, macroB}` in target 7's closed form); the dispatcher opens one more row for them.

**1a (v) size.** Estimate (basis: the analog counts above and the targets' proofs): tagging, untag, normality, shape twist 115; twist cost 70; bridge and `EquivCost` 180; `BASimC'` 50; `baStep_of_simC'`, `s1`, `e1` 155; final step 70; assembly, `BAReach` bridge, closed form, premise provers 150; instances (target 8) 170; header 60: about 1,020 in `RBM3D/Graph/BAStepS.lean`, below the 1,700 threshold, so `BAStepS2.lean` is not written. If the file grows past 1,700 the boundary is after `baStep_of_simC'`: `BAStepS2` = assembly (target 7) and instances (target 8).

### (ii) Concrete nondegenerate instance (Python model of `scost`, `promoteC`, atoms, `LocStd`; not Lean)

Data: `P_B = baPB` (`BASim3:1879`: `E = Fin 2`, `I = Fin 3`, solid `2→3`, `0→2`, `1→4`, waved `4–3`, `M`-dot `2–3`, atom `{2,3}`), the twist `(true,true)` (`BALvl1AInst.locStepB`); the 16 start terms of `fxyPowGraph 2` (`2^{2p}` terms of `G = Ǧ + M`); a `LocStd` graph `L` (`E = Fin 2`, `I = Fin 3`: blue `0→2`, red `1→2`, atom `{3,4}` by `M`-dot, five waved edges). All hypotheses: normal (all circled, no `=`-dot), `CircIffLoop` on the images, `p = 2`, thresholds 4 and 6, external atoms distinct at `L`.
```
$ python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/60e5425b-ae97-4201-b2dc-fc981af93073/scratchpad/T2443/inst.py
P_B atoms: [0, 1, 2, 2, 4]  ord = 1  twist(true,true) atoms: [0, 1, 2, 2, 4]
target 3 (twist): scostA equal at all 15 setoids >= atoms; far-min/all-min P: 1 1  twist: 1 1
target 2 (bridge) P_B      : image has 2 ext + 2 int vertices; scost(img,q)=scostA(comap q) at all 15 setoids; min all/far: 1/1 (A) = 1/1 (img)
target 2 (bridge) twist P_B: image has 2 ext + 2 int vertices; scost(img,q)=scostA(comap q) at all 15 setoids; min all/far: 1/1 (A) = 1/1 (img)
target 2 (BAEquivC): relabelled/reordered image has the same min cost (all, far): 1 1
p=2: 16 start terms; all satisfy locReg6InvA 2 (min all >= 4, min far >= 6): True; (min_all,min_far,ord) over terms: [(4, 6, 2), (4, 6, 3), (4, 6, 4), (4, inf, 2), (5, inf, 3)]
   terms with x, y in distinct atoms (far constraint non-vacuous): 9 of 16
LocStd graph: LocStd = True  atoms [0, 1, 2, 3, 3]  ord = 8  cost at trivial merge (atoms) = 8  min_all = 8  min_far = 8  ext atoms distinct: True
   locReg6InvA-type values at p=2: min_all = 8 >= 2p = 4 and min_far = 8 >= 3p = 6; conclusions: 2p <= ord: True  3p <= ord: True
   image: ext/int = 2 2  ord(img) = 8  scost(img, trivial) = 8  img ext0 != ext1: True
```
The script computes `scost` from the Lean definitions (`skept`, `sIntCls`, `sElemCls`, `lwHalfPat`, `lwElem`, 6a:115-146; atoms from `atomAdj`, `BAVocab:92`; `ord = nS + 2(nW - nA)`), and checks the twist, bridge and relabelling equalities point by point on every setoid, not only the minima. The twisted outputs and the band step at `P2.img` (target 4's second half) are not simulated: they are `baMatch_holds`' instance, `BASimInst.hTB`, `hTC` (R1, merged). No external hypothesis occurs (C1: combinatorial; `m` only labels `LocStep`), so no limit computation applies. Target 7's statement-level instance (`p = 2`) keeps `locReg6InvA` at the start terms (above: all 16 hold), the shape inputs and `BAFinalS` as hypotheses.

### Verdict
- Target 1 (tagging, `untag` iff): PASS. Target 2 (`BABridge`, `BAEquivC` transfer): PASS. Target 3 (twist, shape twist): PASS.
- Target 4 (`BASimC'` at `BALocStepT`): PASS (`BAMatchTw` dropped). Target 5 (`baStep_of_simC'`, `s1` vacuous, `e1`): PASS.
- Target 6 (`BAFinalS` at `LocStd`): PASS (route through `P.img`, no half-edge table). Target 7 (`ba_ord_ge_of_simC'`, closed form): PASS with the e2/macroA/macroB shape inputs kept as hypotheses (O2: priced above 400 lines); proposed change: no frame-normality hypothesis (finding above). Target 8 (instances): PASS.

## (a″) Probe compile — Mon Oct 12 08:43:49 UTC 2026

Probe `RBM3D/Probe/T2443Pins.lean`, branch `t/T2443`, commit `6b5ad59`, 393 lines (limit 400); role prover-max. The Lean tree of `main` (458ec8c) equals the branch base (`git diff --stat c43bdf1 main -- RBM3D RBM3D.lean` prints nothing). Section (a) (i) drops `BAMatchTw` and its three bridges, so they are not compiled; the probe proves target 3 (`baCostTwist_holds`), so that default stands. Run from `Mon Oct 12 08:42:18 UTC 2026` to `Mon Oct 12 08:42:30 UTC 2026` (`date -u` before and after):
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2443 && lake env lean RBM3D/Probe/T2443Pins.lean; echo "exit: $?"
BAFrameStepTN : BTStep
BALocStepT : BTStep
BASimC' : ℂ → BTStep → Prop
BAFinalS : (BAPGraph (Fin 2) → Prop) → Prop
BALocReg6 : Prop
baUntag_locStepT : ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))),
  untag BALocStepT P L ↔ P.g.Normal ∧ BALocStep P L
baNormal_locStepT : BANormal (untag BALocStepT)
baBridge_holds : BABridge
baEquivCost_holds : BAEquivCost
baCostTwist_holds : BACostTwist
baShapeLL_twist : ∀ (sh : BAShape), BAShapeLL sh BAFrameStepTN → BAShapeLL sh BALocStepT
baSimC'_holds : ∀ (m : ℂ), BASimC' m BALocStepT
baStep_of_simC' : ∀ (m : ℂ) (T : BTStep),
  BASimC' m T → (∀ (sh : BAShape), sh ≠ BAShape.band → BAShapeLL sh T) → BAStep (untag T)
baFinalS_holds : ∀ (R : BAPGraph (Fin 2) → Prop), BAFinalS R
ba_ord_ge_of_simC' : ∀ (m : ℂ) (p : ℕ) (T : BTStep) (P0 : BAPGraph (Fin 2)),
  locReg6InvA p P0 →
    BANormal (untag T) →
      BASimC' m T →
        (∀ (sh : BAShape), sh ≠ BAShape.band → BAShapeLL sh T) →
          BAFinalS (BReach (untag T) P0) →
            ∀ (Q : BAPGraph (Fin 2)),
              BReach (untag T) P0 Q →
                locReg6InvA p Q ∧
                  (Q.g.LocStd →
                    2 * ↑p ≤ Q.scalingOrder ∧
                      (¬(atomSetoid Q.g) (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * ↑p ≤ Q.scalingOrder))
@baReach_bReach : ∀ {K : ℤ} {P0 Q : BAPGraph (Fin 2)},
  P0.g.Normal → BAReach K P0 Q → Q.g.Normal ∧ BReach (untag BALocStepT) P0 Q
baLocReg6_of_shapes : BAShapeLL BAShape.s1 BAFrameStepTN → BAShapeLL BAShape.e1 BAFrameStepTN → BALocReg6
@baUntag_locStepT_intro : ∀ {P : BAPGraph (Fin 2)} {L : List (BAPGraph (Fin 2))},
  P.g.Normal → BALocStep P L → untag BALocStepT P L
@baInit_locReg6InvA : ∀ {p : ℕ} {P0 : BAPGraph (Fin 2)},
  P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition → locReg6InvA p P0
theorems of this file: 16; outside the standard axioms: []; unregistered unproved premises in RBM.Graph: []
exit: 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom |^ *axiom " RBM3D/Probe/T2443Pins.lean; echo "grep exit: $?"
grep exit: 1
$ git diff --stat main...t/T2443
 RBM3D/Probe/T2443Pins.lean | 393 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 393 insertions(+)
```
The last output line is the probe's own scan (`run_cmd` at the end of the file): 16 public theorems, none outside `propext`, `Classical.choice`, `Quot.sound`; `RBM.Audit.scanPremises` (the scan of `#assert_rbm_axioms`, `Test/Axioms.lean:425-446`) finds no unregistered unproved premise in `RBM.Graph`. Control, the same file without the two premise provers `baUntag_locStepT_intro`, `baInit_locReg6InvA` (`scratchpad/T2443/ctrl1.lean`):
```
$ lake env lean scratchpad/T2443/ctrl1.lean | tail -2
theorems of this file: 14; outside the standard axioms: []; unregistered unproved premises in RBM.Graph: [RBM.Graph.untag,
 RBM.Graph.locReg6InvA]
```
Statement texts against the check file (item (vi); `scratchpad/T2443/diffstmts2.py` extracts each `T2443_*` body and the probe's text, substitutes the names, normalises whitespace):
```
$ python3 -I scratchpad/T2443/diffstmts2.py
11 of 12 statements IDENTICAL (name substitution, whitespace normalised): FrameT->BAFrameStepTN, LocStepT->BALocStepT, Untag->baUntag_locStepT, Bridge->BABridge, EquivCost->BAEquivCost, CostTwist->BACostTwist, ShapeTwist->baShapeLL_twist, SimC->BASimC', StepOfSimC->baStep_of_simC', Final->BAFinalS, OrdGe->ba_ord_ge_of_simC'
T2443_LocReg6 -> BALocReg6: DIFFERENT
    --- check
    +++ probe
    @@ -2,3 +1,0 @@
    -(∀ (P : BAPGraph (Fin 2)) (outs : List (BAPGraph (Fin 2))), BAFrameStep P outs →
    -P.g.Normal →
    -∀ Q ∈ outs, Q.g.Normal) →
```
New names, declarations found by regex over every `RBM3D/**/*.lean` of each ref (`scratchpad/T2443/grepnames2.py`); `BAExpand.lean` has `section BABridge` (lines 368, 492), `BASim.lean:16` and `BALvl1A.lean:42` mention `BAMatchTw` in docstrings:
```
$ python3 -I scratchpad/T2443/grepnames2.py
main (458ec8c): 493 files; declarations of the new names: 0; mentioned in: BAExpand.lean[BABridge] BALvl1A.lean[BAMatchTw] BASim.lean[BAMatchTw]
t/T2433 (f275032): 478 files; declarations of the new names: 0; mentioned in: BAExpand.lean[BABridge]
t/T2434 (1ac6995): 489 files; declarations of the new names: 0; mentioned in: BAExpand.lean[BABridge] BASim.lean[BAMatchTw]
t/T2435 (e1cdda3): 491 files; declarations of the new names: 0; mentioned in: BAExpand.lean[BABridge] BASim.lean[BAMatchTw]
t/T2441 (eca2d7c): 493 files; declarations of the new names: 0; mentioned in: BAExpand.lean[BABridge] BALvl1A.lean[BAMatchTw] BASim.lean[BAMatchTw]
t/T2442 (0b280c3): 493 files; declarations of the new names: 0; mentioned in: BAExpand.lean[BABridge] BALvl1A.lean[BAMatchTw] BASim.lean[BAMatchTw]
```
Findings (from the output above and the probe file):
1. The twelve statements compile against `main`; eleven equal the check file's. The twelfth, `BALocReg6` (`T2443_LocReg6`), differs by one deleted hypothesis, frame normality, because `baNormal_locStepT : BANormal (untag BALocStepT)` is proved with no hypothesis (every output of every `BAFrameStepT` constructor is an `outsT` of a partition, `BAGraph.partition_normal`; the twist keeps normality, `ba_twist_inv_out`). The check file's version follows by weakening. For the dispatcher: this closed form does not need L3a4's frame-normality conjunct.
2. Proved in the probe (lines 72-285; pins 37-70; instances 286-353): `baUntag_locStepT` (target 1, the `untag` iff), `baNormal_locStepT`, `baBridge_holds`, `baEquivCost_holds` (target 2), `baCostTwist_holds`, `baShapeLL_twist` (target 3), `baSimC'_holds` (target 4, `P' := (P.twist c t).img`, `baMatch_holds`), `baStep_of_simC'` (target 5, probe 137 per output), `baFinalS_holds` (target 6, through `P.img`), `ba_ord_ge_of_simC'` (target 7, probe 95/148), `baReach_bReach`, `baLocReg6_of_shapes`, and the premise provers `baUntag_locStepT_intro`, `baInit_locReg6InvA`.
3. Not in the probe: `BAShapeLL s1 BAFrameStepTN` and `BAShapeLL e1 BAFrameStepTN` (target 5's two closed shapes; hypotheses `hs1`, `he1` of `baLocReg6_of_shapes`); the T2426 O2 inputs for `e2`, `macroA`, `macroB` (the hypothesis of `BALocReg6`; `hX` in the examples of targets 5 and 7); `BAStepS.lean`.
4. Instances (lines 286-353). Discharged: the tags `band`, `e1`, `e2`, `macroA`, `macroB` occur at the twists `(true, true)` of `P_B`, `P_C`; `BALocStepT` holds there (`stepB`, `stepC`); `untag BALocStepT` is R1's `locStepB`, `locStepC`; the band clause of `BASimC'` at both steps; targets 2, 3 at `P_B`; the graph `pL` (`E = Fin 2`, `I = Fin 3`) has `LocStd`, `scalingOrder = 8` and distinct external atoms by `decide`, and `baFinalS_holds` gives `k ≤ ord` for both `far`. Conditional: target 5 at the twist of `P_B` (hypothesis `hX`), target 7 at `p = 2` (hypotheses `hs1`, `he1`, `hX`).
5. Size, item (v): section (a) (v) estimates 790 lines for the proof items (115 + 70 + 180 + 50 + 155 + 70 + 150) and about 1,020 for `BAStepS.lean`. The probe has the same items, without the `s1`, `e1` closure, in 214 lines (target 1: 38, targets 2-3: 91, target 4: 13, target 5: 13, target 6: 20, target 7: 39; `grep -n "^/-! ##"` ranges), the pins in 35 and the instances in 68; its lines are long (`linter.style.longLine` off).
## (b) Script output, stage 1b (role prover-hard, model claude-sonnet-5-5) — Mon Oct 12 09:09:59 UTC 2026

Stage 1b started `Mon Oct 12 08:51:41 UTC 2026` (first `date -u`); commit `e9528ea` on `t/T2443` (only `RBM3D/Graph/BAStepS.lean`, 523 insertions; `date -u` after it: `Mon Oct 12 09:00:15 UTC 2026`). `BAStepS2.lean` is not written.
```
$ wc -l RBM3D/Graph/BAStepS.lean; ls RBM3D/Graph/BAStepS2.lean 2>&1 | tail -1; grep -cE "\bsorry\b|\badmit\b|native_decide|^ *axiom " RBM3D/Graph/BAStepS.lean
523 RBM3D/Graph/BAStepS.lean
ls: RBM3D/Graph/BAStepS2.lean: No such file or directory
0
```
Line count against the stop line: 523 of 2,000 per file (binding); (a) (v) predicted about 1,020 and the 1,700 split threshold. The H134 stop rule did not trigger.
```
$ lake build RBM3D.Graph.BAStepS 2>&1 | tail -2              (build after the last edit, 08:56:20 UTC; output filtered of replayed warnings of other modules)
✔ [3825/3825] Built RBM3D.Graph.BAStepS (7.8s)
Build completed successfully (3825 jobs).
```
Full library: `RBM3D.lean` is unchanged on the branch (the hub adds the root import at merge, CLAUDE.md §3 (A) 4). For the whole `lake build` I added `import RBM3D.Graph.BAStepS` to `RBM3D.lean` temporarily (08:56-08:58 UTC), built, and restored the file from a copy before the commit. `Test/Axioms.lean` is unchanged (`git diff --stat main...t/T2443 -- RBM3D/Test RBM3D.lean` prints nothing):
```
$ lake build 2>&1 > fullbuild.out; grep -c '^error' ...; grep -c '<names>' ...; grep 'axiom audit\|^Build completed' fullbuild.out      (summary line by script)
errors: 0, lines naming the new declarations: 0
info: RBM3D.lean:497:0: axiom audit: 12938 theorems, 4063 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4265 jobs).
```
Axioms (`ax.lean`: `#print axioms` of the 16 public theorems; `ax_scan.lean`: the file plus a `run_cmd` scan):
```
$ lake env lean ax.lean | sed 's/^.* depends on axioms: //' | sort | uniq -c
  16 [propext, Classical.choice, Quot.sound]
$ lake env lean ax_scan.lean | head -1
declarations of this file (theorems and defs, internal details excluded): 24, of which theorems: 16; outside propext/Classical.choice/Quot.sound: []
```
Targets 1-7, extracted by script (`stmts.py`; `:N` is the line in `BAStepS.lean`; theorem: text before the proof; def: whole body; whitespace normalised):
```
[T1] :64 def BAFrameStepTN : BTStep := fun P LT => P.g.Normal ∧ BAFrameStepT P LT
[T1] :67 def BALocStepT : BTStep := fun P LT => P.g.Normal ∧ ∃ (c t : Bool) (LT0 : List (BAShape × BAPGraph (Fin 2))), BAFrameStepT (P.twist c t) LT0 ∧ LT = LT0.map (fun x => (x.1, BAPGraph.twist c t x.2))
[T1] :107 theorem baUntag_locStepT : ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), untag BALocStepT P L ↔ P.g.Normal ∧ BALocStep P L
[T1] :129 theorem baNormal_locStepT : BANormal (untag BALocStepT)
[T1] :137 theorem baUntag_locStepT_intro {P : BAPGraph (Fin 2)} {L : List (BAPGraph (Fin 2))} (hN : P.g.Normal) (h : BALocStep P L) : untag BALocStepT P L
[T1] :141 theorem baInit_locReg6InvA {p : ℕ} {P0 : BAPGraph (Fin 2)} (h : P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition) : locReg6InvA p P0
[T2] :72 def BABridge : Prop := ∀ (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k P ↔ PGraph.LocCostGe far k P.img
[T2] :160 theorem baBridge_holds : BABridge
[T2] :76 def BAEquivCost : Prop := ∀ (R S : PGraph (Fin 2)), R.BAEquivC S → ∀ (far : Bool) (k : ℤ), (R.LocCostGe far k ↔ S.LocCostGe far k)
[T2] :186 theorem baEquivCost_holds : BAEquivCost
[T3] :80 def BACostTwist : Prop := ∀ (c t : Bool) (P : BAPGraph (Fin 2)) (far : Bool) (k : ℤ), locCostGeA far k (P.twist c t) ↔ locCostGeA far k P
[T3] :225 theorem baCostTwist_holds : BACostTwist
[T3] :232 theorem baShapeLL_twist : ∀ sh : BAShape, BAShapeLL sh BAFrameStepTN → BAShapeLL sh BALocStepT
[T4] :84 def BASimC' (m : ℂ) (T : BTStep) : Prop := ∀ P LT, T P LT → ∃ P' : PGraph (Fin 2), P'.g.Normal ∧ LGraph.CircIffLoop P'.g ∧ (∀ far k, locCostGeA far k P → P'.LocCostGe far k) ∧ ∀ Q, (BAShape.band, Q) ∈ LT → ∃ L' : List (PGraph (Fin 2)), LocStep m P' L' ∧ ∃ R ∈ L', ∀ far k, R.LocCostGe far k → locCostGeA far k Q
[T4] :244 theorem baSimC'_holds (m : ℂ) : BASimC' m BALocStepT
[T5] :258 theorem baStep_of_simC' : ∀ (m : ℂ) (T : BTStep), BASimC' m T → (∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) → BAStep (untag T)
[T5] :353 theorem baShapeLL_s1_tn : BAShapeLL BAShape.s1 BAFrameStepTN
[T5] :358 theorem baShapeLL_e1_tn : BAShapeLL BAShape.e1 BAFrameStepTN
[T6] :91 def BAFinalS (R : BAPGraph (Fin 2) → Prop) : Prop := ∀ (P : BAPGraph (Fin 2)) (k : ℤ), R P → P.g.LocStd → (locCostGeA false k P → k ≤ P.scalingOrder) ∧ (¬ atomSetoid P.g (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) → locCostGeA true k P → k ≤ P.scalingOrder)
[T6] :368 theorem baFinalS_holds (R : BAPGraph (Fin 2) → Prop) : BAFinalS R
[T7] :389 theorem ba_ord_ge_of_simC' : ∀ (m : ℂ) (p : ℕ) (T : BTStep) (P0 : BAPGraph (Fin 2)), locReg6InvA p P0 → BANormal (untag T) → BASimC' m T → (∀ sh, sh ≠ BAShape.band → BAShapeLL sh T) → BAFinalS (BReach (untag T) P0) → ∀ Q, BReach (untag T) P0 Q → locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder ∧ (¬
    atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))
[T7] :403 theorem baReach_bReach {K : ℤ} {P0 Q : BAPGraph (Fin 2)} (h0 : P0.g.Normal) (h : BAReach K P0 Q) : Q.g.Normal ∧ BReach (untag BALocStepT) P0 Q
[T7] :98 def BALocReg6 : Prop := ∀ (p : ℕ) (P0 : BAPGraph (Fin 2)), P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition → (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) → ∀ (K : ℤ) (Q : BAPGraph (Fin 2)), BAReach K P0 Q → locReg6InvA p Q ∧ (Q.g.LocStd → 2 * (p : ℤ) ≤ Q.scalingOrder
    ∧ (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder))
[T7] :413 theorem baLocReg6_reach : BALocReg6
```
```
$ python3 -I diffprobe.py
21 of 21 declarations: statement text IDENTICAL in the probe and in BAStepS.lean (whitespace normalised; theorem: text before the proof, def: whole body)
not identical: none
baLocReg6_reach vs probe baLocReg6_of_shapes, text before the proof:  probe=[(hs1 : BAShapeLL BAShape.s1 BAFrameStepTN) (he1 : BAShapeLL BAShape.e1 BAFrameStepTN) : BALocReg6]  final=[: BALocReg6]
$ python3 -I diffcheck_final.py        (check file against BAStepS.lean, names substituted; `+++ BAStepS` is the new file)
11 of 12 statements IDENTICAL (name substitution, whitespace normalised): FrameT->BAFrameStepTN, LocStepT->BALocStepT, Untag->baUntag_locStepT, Bridge->BABridge, EquivCost->BAEquivCost, CostTwist->BACostTwist, ShapeTwist->baShapeLL_twist, SimC->BASimC', StepOfSimC->baStep_of_simC', Final->BAFinalS, OrdGe->ba_ord_ge_of_simC'
T2443_LocReg6 -> BALocReg6: DIFFERENT
    --- check
    +++ BAStepS
    @@ -2,3 +1,0 @@
    -(∀ (P : BAPGraph (Fin 2)) (outs : List (BAPGraph (Fin 2))), BAFrameStep P outs →
    -P.g.Normal →
    -∀ Q ∈ outs, Q.g.Normal) →
$ lake env lean docs/tickets/checks/T2443-check.lean > check.out 2>&1; echo "exit $? errors $(grep -c error check.out)"
exit 0 errors 0
```
The compiled nonempty instances (section 8 of `BAStepS.lean`; compiled in the builds above):
```
444:example : (BAShape.band ∈ BAStepS_LTB.map Prod.fst ∧ BAShape.e2 ∈ BAStepS_LTB.map Prod.fst ∧ BAShape.macroA ∈ BAStepS_LTB.map 
450:example : untag BALocStepT ((baPG baPB).twist true true) (((baPG baPB).withinOuts pB).map (BAPGraph.twist true true)) ∧
455:example (m : ℂ) : (∃ P' : PGraph (Fin 2), P'.g.Normal ∧ ∃ Q, (BAShape.band, Q) ∈ BAStepS_LTB ∧ ∃ L' : List (PGraph (Fin 2)), L
466:example (far : Bool) (k : ℤ) : (locCostGeA far k (baPG baPB) ↔ PGraph.LocCostGe far k (baPG baPB).img) ∧
472:example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) (far : Bool) (k 
488:example (far : Bool) (k : ℤ) (hk : locCostGeA far k ((baPG baPC).twist true true)) : ∃ Q, (BAShape.e1, Q) ∈ BAStepS_LTC ∧ locC
498:example (far : Bool) (k : ℤ) (hk : locCostGeA far k BAStepS_pL) : BAStepS_pL.g.LocStd ∧ BAStepS_pL.scalingOrder = 8 ∧
508:example (hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) :
```
Data: targets 1 and 4 at the twists `(true, true)` of `baPG baPB` (`within`, `BAStepS_stepB`) and `baPG baPC` (`ggSplit`, `j = 0`, `BAStepS_stepC`; the tags `band`, `e1`, `e2`, `macroA`, `macroB` occur, by `decide +kernel`); target 2 at `baPG baPB` (and `BAEquivC` at the reflexive pair); target 3 at its twist; target 5 at `BAStepS_stepB` and at an `e1` output of `BAStepS_stepC`; target 6 at `BAStepS_pL` (`E = Fin 2`, `I = Fin 3`: `LocStd`, `scalingOrder = 8`, distinct external atoms, by `decide`); target 7 at `p = 2` (a start term exists by `decide`; `locReg6InvA 2 P0` by `baInit_locReg6InvA`; the closed form at every `BAReach`). The one hypothesis kept in the examples is `hX`, the shape inputs `e2`, `macroA`, `macroB` of T2426 audit O2 (an unproved pin of another row); every deterministic hypothesis is discharged.
Name clash (`clash.py`: declarations of the 24 new public names in every non-probe `RBM3D/**/*.lean` of each ref; last line: `git grep -n BAStepS <ref> -- RBM3D | wc -l`):
```
main (ec795c5): 0 t/T2433 (f275032): 0 t/T2434 (2a26066): 0 t/T2435 (e1cdda3): 0 t/T2441 (7d3a5e2): 0 t/T2442 (0b280c3): 0 t/T2443 (e9528ea): 0
main:0 t/T2433:0 t/T2434:0 t/T2435:0 t/T2441:0 t/T2442:0
```
Narrative (ports: none, stage 1b read nothing under `../RBM1D` or `../RBM2D`, no diff-stat; helpers are `private` with the stem `BAStepS_`).
- `BAMatchTw` (1a (i)): not used, not declared (`grep -nE "(def|theorem|lemma) +[A-Za-z_.']*(BAMatchTw|img_twist)" BAStepS.lean` prints nothing); `baCostTwist_holds` compiled, so the default route `P' := (P.twist c t).img` stands. O2 (1a (iv)): the three inputs stay hypotheses of `BALocReg6` (the 1a-audit applied the ticket's rule: priced about 1,200-1,600 lines, above 400; 1a-audit §6 hands the new row to the dispatcher). The shapes `s1` and `e1` are closed here.
- New in the file against the probe: `baShapeLL_s1_tn`, `baShapeLL_e1_tn` through `BAStepS_frameT_tags` (every output of a `BAFrameStepT` constructor is an `outsT` of `tagStd` (`e2`/`band`), `tagT1` (`e1`/`band`) or a constant `macroA`/`macroB`, so none is `s1`; an `e1` output is `BAScost_pack P Q0` with `Q0` in the partition of `lanlwT1 P.g p`, the hypothesis of `baShapeLL_e1`), `baLocReg6_reach` (the closed form without `hs1`, `he1`), and the renamed `private` instance data. The other proofs are the probe's.
- Premise provers (`Test/Axioms.lean:390-445`; the control `ctrl1.lean` of (a″) shows the scan failing on `untag` and `locReg6InvA` without them): `untag` at `BALocStepT`: `baUntag_locStepT_intro`; `BANormal (untag BALocStepT)`: `baNormal_locStepT`; `locReg6InvA` at start terms: `baInit_locReg6InvA`; `BASimC'`: `baSimC'_holds`; `BAFinalS`: `baFinalS_holds`; `BAStep (untag T)`: `baStep_of_simC'`; `BALocReg6`: `baLocReg6_reach`. The full build above ran `#assert_rbm_axioms` without error.
- `BALocReg6` has no frame-normality hypothesis: `baNormal_locStepT` is unconditional (every output of a constructor is an element of a partition, `BAGraph.partition_normal`). It is stronger than the check file's form, which follows by weakening (1a-audit §2). The dispatcher note about an extra corollary from L3a4's `BAstepMono` is moot: `T2442.state` says merged at `Mon Oct 12 08:51:53 UTC 2026`, the branch base `c43bdf1` has no `BALvl1B`, and the closed form does not use frame normality.
- Special-case caveat (CLAUDE.md §5.6): `baLocReg6_reach` is conditional on the O2 shape inputs; it is not a hypothesis-free statement of (6) along `BAReach`.
## (c) Verified Mathlib and core names used (all 17 `#check` printed a type, run `Mon Oct 12 09:01:33 UTC 2026`; none searched for as absent)
Function.surjInv, Function.surjInv_eq, Setoid.comap, List.mem_map, List.mem_append, List.forall_mem_append, List.mem_singleton, List.exists_mem_of_ne_nil, Sum.map_surjective, List.Perm.length_eq, List.Forall₂.length_eq, le_of_le_of_eq, List.map_congr_left, List.map_map, Function.comp_def, List.length_map, Prod.mk.inj.
## (d) Open issues and paper-delta candidates
1. T2426 audit O2 inputs (`BAShapeLL sh BAFrameStepTN` for `sh` in `e2`, `macroA`, `macroB`: `BAScostLL` at the builder terms and the stage-2 implications at the packed transfer graphs, priced in (a) (iv)) are unproved; the row (stage L 50 to 51) is the dispatcher's. `BALocReg6` and `hX` in the target 5 and 7 instances carry them.
2. `T2443a`: `BAFinalS` reads the atom-level `P.g.LocStd` where the merged `BAFinal` reads vertex-level `locStdA` (L4-C3). `T2443b`: `BASimC'` is per output (`P'` per step, `L'` per `band` output); the literal one-`L'` `BASimC` is not stated (T2423 T3). `T2443c`: `BALocReg6` drops the check file's frame-normality hypothesis. `T2443d`: `BALocReg6` is conditional on the O2 inputs (item 1).
