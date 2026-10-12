Auditor model: claude-opus-5-5

# T2423 1a-audit round 2 (design gate, after one rule-(B) repair), Sun Oct 11 14:10:32 UTC 2026

Inputs: ticket `docs/tickets/T2423.md`; `docs/reports/T2423-prove.md` sections (a), (a″), (a′) (297 lines); round-1 `Required for resubmission` items 1-6; branch `t/T2423` at `796a2dc` (unchanged since round 1; (a′) says no probe statement changes); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2423-1a-audit2` (detached at `796a2dc`); scratch `SP = <scratchpad>/T2423/`, my outputs in `SP/aud2/`.

**Verdict: PASS, needs dispatcher sign-off.** All six round-1 items are answered, and every new script reproduces exactly. The probe and the check file compile (exit 0, standard three axioms). No binding stop line is hit: the predicted sizes are 1,680 and 1,770 lines against 2,000 per file. No band shape fails. Two scope decisions are left open by the report itself (§3 S1, S2); they are the dispatcher's, not the auditor's.

## 1. Probe and check file
```
$ cd RBM3D-wt/T2423-1a-audit2; git diff --stat 4ccca7b...HEAD
 RBM3D/Probe/T2423Pins.lean | 352 +++++++++++++++++++++++++++++++++++++++++++++
$ wc -l < RBM3D/Probe/T2423Pins.lean; grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2423Pins.lean
     352
0
$ date -u; lake env lean RBM3D/Probe/T2423Pins.lean > aud2/probe.out 2>&1; echo exit=$?; date -u; grep -iE "error|warning|axioms" aud2/probe.out
Sun Oct 11 14:07:06 UTC 2026
exit=0
Sun Oct 11 14:07:38 UTC 2026
'RBM.Graph.BAMatch' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAExtraGood' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAFrameStepT_untag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAsim' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAsim'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.BAFrameStepT' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.PGraph.BAEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2423-check.lean > aud2/check.out 2>&1; echo exit=$?; grep -ci error aud2/check.out
exit=0
0
```
Pinned statements (probe 150-195), as in round 1: `BAMatch` is per output and at frame level, with the band step at `P.img`. `BAExtraGood` is Lemma E for `e1`/`e2`. `BAsim` is T2395 probe 263 verbatim. `BAsim'` uses `T` normal with `T.baInv = P.baInv`, which is the form the ticket's item 2 allows. The instances discharge every deterministic hypothesis at nondegenerate data `P_A`-`P_E` (|V| = 5, nExt = 2).

## 2. Round-2 scripts rerun (`cd SP; python3 <s>.py > aud2/<s>.out`, all exit 0; every line equals (a′))
```
$ python3 lines.py | tail -4
BASim   total predicted  1680   stop line 2000   margin  320 (16%)   +30% would be  2184
BASim2  total predicted  1770   stop line 2000   margin  230 (12%)   +30% would be  2301
both files 3450  (ticket expects 2,000-2,400; T2395 row R1 central 1,170; landed/central measured: R0 1.39 = 1247/900, L2c1 2.04 = 1941/950)
split if a file exceeds: Lemma E (C3 615) and the BAsim' assembly (C4 400) to a third file Graph/BASim3.lean (1,015): BASim 1680 / BASim2 755 / BASim3 1015
$ python3 lemE_summary.py
family          outputs     id  merge fixed split jmax minraw mindord(split) E*viol
edge:L1              228     228    114     0   114    1      1             2      0
edge:LD              896     896    416     0   416    3      1             0      0
gg:A1                680     680    420   420     0    0      0             -      0
gg:A4               1360    1360    680     0   680    1      1             2      0
gg:A5               2720    2720    420     0   420    2      1             1      0
gg:AD               5376    5376   2608     0  2608    3      1             0      0
gg:B2               2720    2720    420     0   420    2      1             1      0
gg:BD               5376    5376    992     0   992    3      1             1      0
ggSplit:X.L1        1696    1696    848     0   848    1      1             2      0
ggSplit:X.LD        6720    6720   3124     0  3124    3      1             0      0
ggSplit:X.d1        3392    3392    516     0   516    2      1             1      0
ggSplit:X.d4         848     848    516   516     0    0      0             -      0
weight:lw2.D         672     672    256     0   256    3      1             0      0
weight:lw4.D         672     672     48     0    48    3      1             2      0
within:W.D           960     960    304     0   304    3      1             0      0
no identification of P-atoms at all (merge = 0): gg:A2, gg:A3, gg:B1, ggSplit:X.d2, ggSplit:X.d3, weight:lw2.leaf, weight:lw4.leaf, within:W.first; E*viol total 0
$ python3 lemE_eq.py
equality cases (j, kappa, lambda): count {(1, 0, 1): 26, (3, 1, 1): 92, (3, 1, 2): 4} | min lambda 1 | families ['AD', 'LD', 'W.D', 'X.LD', 'lw2.D']
$ python3 selrule.py
band-tagged outputs matched by the rule step / band-tagged, per term: A1 59/59  A2 99/99  A3 99/99  A4 99/99  A5 356/356  AD 482/482  B1 198/198  B2 356/356  BD 708/708
$ python3 partner.py | python3 partner_cond.py
edge     L1>E.T1  LD>E.D/E.P5/E.P3/E.P4/E.P6
gg       A1>R2  A2>R2  A3>R2  A4>R3/R5  A5>R5/R3/R7  AD>R7/R5  B1>R4/R6/R8  B2>R6/R4/R8  BD>R8/R4/R6
ggSplit  X.L1>R3/R5  X.LD>R7  X.d1>R5/R3/R7  X.d2>R5  X.d3>R5/R7
weight   lw2.D>T3  lw2.leaf>T1  lw4.D>T4  lw4.leaf>T2
within   W.D>T3  W.first>T1
$ python3 trhyp.py
within   steps 122 | M1 frame step at tr 122 | M2 tr normal 122 | M3 baInv(tr)=baInv(P) 122
ggSplit  steps  99 | M1 frame step at tr  99 | M2 tr normal  99 | M3 baInv(tr)=baInv(P)  99
$ python3 d4check.py
X.d2 848 outputs, ord rises 848 | X.d3 848 outputs, ord rises 848
X.d4 848 outputs = ord rises 387 + (ord equal, nExt falls) 129 + (ord equal, nExt equal) 332 ; of the last: [y]=[y'] same atom 332, inv(Q) = inv of a band R2 output at img P 332
min Delta ord: {('X.d2',): 1, ('X.d3',): 1, ('X.d4',): 0}
```
Script content checked. `lines.py` hard-codes the estimates; it counts only the basis ranges, and it says so. In `lemE_summary.py` the `id` column checks `nS Q = nS T0 − j`, `nW` unchanged and `nExt T0 ≤ nExt P` (κ is defined from nA). The substantive check is `E*viol`, a direct test of `ord Q > ord P ∨ nExt Q < nExt P` on every identification. `d4check.py` and `trhyp.py` test exactly the claims M1-M3 and the `X.d2`-`X.d4` claims.

Every merged name that (a′) cites exists on `main` `46120c3`, at the cited line (`git grep` of the declaration line):
```
lwExpSim_equivs LWExpSim:691 | LGraph.counters_relabel_equiv LWVocab:2114 | lwSplit_map LWExpSim:60 | lvl1_split_last LWLvl1:4220
BAAtomic_solidAt 624, BAAtomic_charge 633, BAAtomic_fm 559, BAAtomic_exists_inr_vmap 652 (all private, BAAtomic) | BAAtomic_img_solid 269 | img_normal 308 | img95_equiv_gen 805
BAAtomic_vmap_eq_iff 199 | BAAtomic_promoteC_vmap_eq_sameAtom 229 | BAAtomic_vmap_isRight_iff 213 | BASymm1_twist_atom BASymm1:101 | lwSymmTwistS LWSymm:167 | scost_perm LocalRegular6a:309
BAWeightOp_{nExt_add_nA 1541, packMerge_counters 1385, ext_normal 1665, split3 1398, D4_split 1508, nA_le 887, mono_aux 1794} (private) | lw_counters 1680 | lw_mono 1815
BAGGOp_kappa 1533 | BAGGOp_addM_cnt_all 1553 (private) | gg_counters 1621 | gg_raw 1636 | gg_scalingOrderG 1666 | gg_mono 1702 | BAGGOp_Mono 1608 | lanlw_ord BAExpandWOrd:781 | lanlw_scalingOrderG 803
open private idiom: BAGGOp.lean:47-55 (`open private BAWeightOp_… from RBM3D.Graph.BAWeightOp`): 23 `open private` lines on main
```

## 3. Round-1 "Required for resubmission" against (a′)
| R1 item | (a′) | status |
|---|---|---|
| 1 (v) lines per file vs 2,000 | §1: per section B1-B7 / C1-C5; 1,680 / 1,770; split rule C3+C4 → `BASim3` | **met**. Not a stop line. See S2 |
| 2 (iii) Lemma E proof plan | §2: E1 counter identity `ord Q = ord P + raw − j + 2κ`, `κ+λ` = rank; E2 merged raw/mono inputs; E3 `packMerge` (normal T′, no `=` dots); E4 fixed vs split; E5 per-family omega; E6 `W−1` terms by the term lists | **met**: the argument closes. Δord = raw − j + 2κ with raw ≥ 1 (split families). An equality needs κ + λ ≥ rank ≥ 1 (and ≥ 2 at j = 3), so λ ≥ 1. The data agree: `lemE_eq` min λ = 1. A1 and X.d4 (fixed) go by κ_f = 0 ⇒ both atoms external |
| 3 (ii) band term, selector, eE/eI, hyps, solidAt | §3: table (term → band term, selector, φ on new vertices); LemQ + `lwExpSim_equivs` gives eE, eI as fibres of ψ = `Hc.vmap ∘ φ`; choice rule c(S); B4 per kind; `open private BAAtomic_solidAt` (corrects (a″)) | **met** (a constructive recipe, not literal bijections, but sufficient for 1b) |
| 4 item 2: `BAsim'` derivation | §4: case on tag; M1 `T_tr`, `outsT` rfl; M2; M3; M4 via `BAMatch`/`BAExtraGood` at `T_tr`; L-inv; X.d2/X.d3 ord ≥ +1; X.d4 = A1 pattern, the κ = 0, [y]=[y′] case matched by an R2 invariant tuple (332/332) | **met** |
| 5 item 1 at `BALocStep` level | §5: "R1 delivers the frame level only"; pseudo-Lean `BAMatchTw`; needs `img_twist`, `BAEquiv.twist`, `partition (twist Γ) ≅ (partition Γ).map twist` (none on main: grep exit 1); owner "the dispatcher's decision" (suggests L3a2/L3a3) | **met as written**, but this narrows a binding item: S1 |
| 6 item 3 per-output `BASimC'` | §6: pseudo-Lean with `∃ L'` inside `∀ Q`; `baStep_of_simC'` is the old proof with one `obtain` changed | **met** |

Stage-1a deliverables overall: (i) met at frame level (S1). (ii) met. (iii) met (check and plan). (iv) met: no failing band shape, 0 unmatched in the exhaustive and random runs. (v) met.

**Dispatcher decisions (sign-off, H183 (3)):**
- **S1 (binding item 1, scope).** Ticket item 1 ("What R1 delivers", binding) asks for the matching "for each step `BALocStep P outs` … at `P' ≅ img P`".
  - R1 proves it only at frame level (`BAMatch` at `P.img` of the graph that the frame step runs on).
  - The `BALocStep`-level corollary `BAMatchTw` and its three bridge lemmas get no row. (a′) §5 says "the row owner is the dispatcher's decision".
  - Frame level suffices for `BAsim` / `ba_lvl1StepGood_of_sim`, which consume it at `P.twist c t`. `BASimC'` (item 6) uses `P' := P.img`, and so assumes the `BTStep` is at frame level.
  - Decide: R1 frame-level only, with `BAMatchTw` assigned to a named row (L3a2/L3a3 or L3b4′). Or R1 also proves `BAMatchTw`; in that case 1b compiles it against `main` (`BASymm1` merged `3dbb04d`).
- **S2 (third file).** The predicted total is 3,450, against the ticket's 2,000-2,400 and T2395's R1 central 1,170. The margins are 16% and 12%; with +30% both files pass 2,000. The report's contingency is to split C3 + C4 into `Graph/BASim3.lean` "if a file passes 1,700 at 1b mid-way". That file is not a sole writable file today, so without a decision 1b would end BLOCKED mid-way. Decide whether to name `Graph/BASim3.lean` now (the report recommends this).

## 4. Observations (no verdict impact)
- O1. `T2423-prove.md` already has 297 lines (CLAUDE.md §6 limit 300; ticket "Report: ≤ 250 lines"). Section (b) at 1b cannot fit unless (a)/(a″)/(a′) are compressed or the dispatcher relaxes the limit.
- O2. The probe's base is `4ccca7b`; `main` is `46120c3`. 1b re-checks the names against `main` (ticket (i)). T2426 (running) also defines `BAShape`/`BTStep`: whichever merges second imports them (both tickets' sibling scans say so).
- O3. Paper-delta candidate `T2423a` (F1: `BAShape.s1` never assigned; BA `A1` = band R2 `(δ,m)`) stays proposed. No new Lean/paper statement difference appears in (a′).
- O4. (a′) adds unpinned names `PGraph.BAEquivC` and `BAPGraph.twist`. At 1b they need the `BASim`/`BASim2` stem or `private`, unless the dispatcher pins them (rule (E)).
