Auditor model: claude-opus-5-5

# T2426 audit (round 1) — BA-L L3b3′ `BAScostS′`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2426-audit1`, detached at `t/T2426` = `1140fac` (base `3dbb04d`; main = `4bd65c3`). Written Sun Oct 11 15:09:49 UTC 2026 (`date -u`). Scratch: scratchpad `T2426/`.

## 1. Diff, build, hygiene, axioms
```
$ git diff --name-status main...t/T2426
A	RBM3D/Graph/BAScost.lean
A	RBM3D/Graph/BAScost2.lean
$ wc -l RBM3D/Graph/BAScost.lean RBM3D/Graph/BAScost2.lean
    1530 RBM3D/Graph/BAScost.lean
     225 RBM3D/Graph/BAScost2.lean            (stop line 2,000 per file: not reached)
$ lake build RBM3D.Graph.BAScost RBM3D.Graph.BAScost2 ; grep error/warning lines for the two files
✔ [3814/3815] Built RBM3D.Graph.BAScost (4.7s)
✔ [3815/3815] Built RBM3D.Graph.BAScost2 (2.6s)
Build completed successfully (3815 jobs).        exit=0   (no error line; no warning line for BAScost*.lean)
$ lake env lean docs/tickets/checks/T2426-check.lean ; echo check_exit=$?
check_exit=0
$ grep -cE "sorry|admit|native_decide|^axiom" (both files)          0 / 0
$ grep -cE "κ|ρ|g0|Im m|Ψ|\(m : ℂ\)" (both files, C1)               0 / 0
$ lake env lean Ax.lean     (collectAxioms over every non-internal constant of the two modules)
185 constants; axiom sets: [([Classical.choice, Quot.sound, propext], 134), ([Quot.sound, propext], 1), ([propext], 17), ([], 33)]
$ name-clash scan: 126 declarations of the two files against `def|theorem|lemma|abbrev|inductive|structure <name>` on main (4bd65c3)
declaration clashes on main (4bd65c3): 0
```
Only the two sole writable files are touched; `RBM3D.lean` is left to the hub; no frozen signature touched.

## 2. Target 1 — vocabulary vs the pin (`t/T2397:RBM3D/Probe/T2397Pins.lean`), docstrings/comments stripped, whitespace normalised
```
$ python3 vd.py probe.lean RBM3D/Graph/BAScost.lean
scostA identical | locStdA identical | locCostGeA identical | locReg6InvA identical | BAInit identical | BAFinal identical
BAStep identical | BANormal identical | BAScostLL identical | BAScostLL.trans identical | BTStep identical | untag identical | BAShapeLL identical
BReach           DIFF
   probe:  inductive BReach (BStep : …) (P0 : BAPGraph (Fin 2)) : BAPGraph (Fin 2) → Prop | refl : BReach BStep P0 P0 | step {Q R} {L} : BReach BStep P0 Q → BStep Q L → R ∈ L → BReach BStep P0 R
   branch: def BReach (BStep : …) (P0 : BAPGraph (Fin 2)) : BAPGraph (Fin 2) → Prop := Relation.ReflTransGen (fun Q R => ∃ L, BStep Q L ∧ R ∈ L) P0
BAShape          DIFF
   probe:  inductive BAShape | band | s1 | e1 | e2 | macroA | macroB
   branch: inductive BAShape | band | s1 | e1 | e2 | macroA | macroB deriving DecidableEq
```
`atomSetoid`/`promoteC` are not redefined (imported from `Graph/BAAtomic`). Both differences checked by compiling (`BR.lean`, imports `RBM3D.Graph.BAScost2`):
```
theorem iff : BReach BStep P0 Q ↔ BReachI BStep P0 Q      -- BReachI = the probe's inductive, copied verbatim; proved both ways by `induction`
theorem ba_ord_ge …                                       -- the probe's statement and proof (T2397Pins), verbatim, against the branch vocabulary
'RBM.Graph.AuditT2426.iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Graph.AuditT2426.ba_ord_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
```
So `BReach` is logically equivalent to the pin, keeps the constructor names `BReach.refl`/`BReach.step`, and `induction hQ with | refl | step …` works (`@[induction_eliminator] BReach.ind`). Reason given in the report: the inductive form trips `#assert_rbm_axioms`' premise scan (`RBM3D/Test/Axioms.lean:257-258` registers `lvl1Split.below`, `Lvl1Reach.below` for the same reason; that file is not writable here). `deriving DecidableEq` adds an instance only (T2423's probe has it too, `T2423Pins.lean:74`). Covered by delta candidate `T2426c`. **Target 1: PASS.**

## 3. Targets 2–4 — statements (extracted from the branch)
```
BAScost.lean:465  theorem BAScost_splitG_le (T : BAGraph E I) {Q} (hQ : Q ∈ T.splitG) (s : Setoid (E ⊕ I)) (hs : atomSetoid Q ≤ s) : scostA T s ≤ scostA Q s
BAScost.lean:487  theorem BAScostLL_splitG (T : BAGraph E I) {Q} (hQ : Q ∈ T.splitG) : BAScostLL T Q
BAScost.lean:1305 theorem BAScostLL_E2 {Γ : BAGraph E I} {X : BAGraph E I'} (hX : BAScostLL Γ X) {Q} (hQ : Q ∈ X.splitG) : BAScostLL Γ Q
BAScost.lean:836  theorem BAScostLL_S1 (Γ) (p q) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hp1 : p.1.σ = true ∧ p.1.circ = true)
                    (hq1 : q.1.σ = true ∧ q.1.circ = true) (hxy : q.1.dst = p.1.src) (hwf1 : Γ.sameAtom p.1.src p.1.dst = false)
                    (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) : BAScostLL Γ (BAGGOp_A1 Γ p q)
BAScost.lean:1140 theorem BAScostLL_lanlwT1 (Γ) (p) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true) : BAScostLL Γ (BAGraph.lanlwT1 Γ p)
BAScost.lean:1299 theorem BAScostLL_E1 (Γ) (p) (hp) (hp1) : ∀ Q ∈ (BAGraph.lanlwT1 Γ p).splitG, BAScostLL Γ Q
BAScost.lean:1057 theorem BAScostLL_macroA (Γ) (p) (hp : p ∈ lwSplit Γ.solid) (hp1 : p.1.σ = true ∧ p.1.circ = true) : BAScostLL Γ (Γ.BAScost_trA p)
BAScost.lean:1237 theorem BAScostLL_macroB (Γ) (p q) (hp) (hq : q ∈ lwSplit p.2) (hp1) (hq1 : q blue circled) (hsame : Γ.sameAtom p.1.src q.1.dst = true)
                    (hwf1 : Γ.sameAtom p.1.src p.1.dst = false) (hwf2 : Γ.sameAtom q.1.src q.1.dst = false) : BAScostLL Γ (Γ.BAScost_trB p q)
BAScost.lean:582  theorem baInit_holds (p : ℕ) : BAInit p
BAScost.lean:680  theorem BAScost_locCostGeA_term (P) (T : BAGraph P.E' I'') (far k) (hLL : BAScostLL P.g T) (hk : locCostGeA far k P) :
                    ∀ Q0 ∈ T.partition, locCostGeA far k (BAScost_pack P Q0)
```
Against the ticket's mathematics and the consumer frame (`t/T2423` probe `BAFrameStep`, `796a2dc`):
- **Lemma B (T2)**: every `Q ∈ T.splitG`, no side condition, `s₀ = s`; `E2` = Lemma B composed with the parent term's local lemma (design T2397 §6 l.102: "BA Lemma B … which also carries e2"; E14 item "Lemma B with E2"). PASS.
- **S1**: builder output `BAGGOp_A1` = head of `gg2` (`BAGGOp.lean:73-78,102`); hypotheses = the `gg` constructor's (`T2423Pins:58-63`: `p`, `q` blue circled, `p.1.src = x = q.1.dst`, `hwf` for every edge). No `[y] ≠ [y']` assumed: stronger than "y, y′ in two atoms". PASS.
- **E1**: every term of `G = Ǧ + M` on `lanlwT1`, both regimes, no atom hypothesis. PASS.
- **macroA / macroB intermediates**: `BAScost_trA`, `BAScost_trB` are, after substituting the `let`s, the probe's transfer graphs `tr`:
```
t/T2423 withinOuts: let e := bpS true (bpv 1) (bpv 1); tr := BAGraph.ext 2 Γ p.2 [e] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]
t/T2426 trA       : BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]
t/T2423 splitOuts : dq s md := BAGraph.ext 2 Γ q.2 s [bpW false (bpv 0) (bpv 1)] (bpM a (bpv 0) :: md); tr := dq [bpS true y' (bpv 1), bpS true (bpv 1) y] [bpM (bpv 0) a']
t/T2426 trB       : BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)]
```
  macroA has no atom hypothesis. macroB's `hsame`, `hwf1`, `hwf2`, blue `q` are implied by the `ggSplit` constructor (`T2423Pins:64-70`: `q.1.σ = true`, `hsame`, `hwf` for all edges); a red `q` does not occur there (open issue (d)3 of the prove report). No new `Dmove`-size primitive (`scostLL_moveSC` 6c:1123). PASS.
- **BAInit (T4)**: the pinned `def BAInit` (identical, §2), proved for every `p`. PASS.
- **Packed forms** (`BAScost2.lean:70-127`): `BAShapeLL sh T` is a pinned `def` with no hypothesis, false for an arbitrary `T`; each `baShapeLL_*` assumes that the `sh`-tagged outputs of `T` are `BAScost_pack P Q0` with `Q0 ∈ X.partition`, the packing of `T2423`'s `outsT` (`BAGraph.partition = splitG.map packMerge`, `BAVocab.lean:229-231`). `s1`, `e1`: nothing else assumed. `e2`, macroB disjunct 2: `BAScostLL P.g X` for the parent builder term is an input. `macroA`, `macroB` disjunct 1: the stage-2 implication `locCostGeA (pack P Q0) → locCostGeA Q` is an input; the BA-only step `P → tr` is proved. Explicit in the signatures; mirrors `localReg6d_locCostGe_term` (6d:955, takes `hLL` as hypothesis). See observation O2.

## 4. Hidden hypotheses, vacuity, cycles
- New structure `BAScost_Term P` (`BAScost2.lean:46`): fields `I'' : Type`, two instances, `X : BAGraph P.E' I''`. No `Prop` field. No other structure/class.
- Imports: `BAAtomic`, `LocalRegular6d`, `BAWeightOp`, `BAGGOp` (all on main); `BAScost2` imports only `BAScost`. No import of probes or unmerged branches; no cycle.
- No external hypothesis (C1: combinatorial only; no limit check needed).
- Vacuity: the term lemmas carry only builder-shape hypotheses, all satisfied at the instances below. `baShapeLL_s1` is vacuous under T2423's present tagging (no `s1` tag assigned, T2423 (a) F1); stated as the ticket asks, recorded in the prove report (d)2.

## 5. Compiled nonempty instances (all in the two files; built in §1)
```
BAScost.lean:1427 example : BAScostLL gs (BAGGOp_A1 gs ps qs) := BAScostLL_S1 gs ps qs ps_mem qs_mem ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl gs_wf1 gs_wf2
BAScost.lean:1431 example : ∀ Q ∈ (BAGraph.lanlwT1 gs ps).splitG, BAScostLL gs Q := BAScostLL_E1 gs ps ps_mem ⟨rfl, rfl⟩
BAScost.lean:1434 example : ∃ Q ∈ (lanlwT1 gs ps).splitG, Q.sameAtom (x) (y) = true ∧ gs.sameAtom ps.1.src ps.1.dst = false := by decide   (extra output exists)
BAScost.lean:1438 example : BAScostLL gw (BAGraph.lanlwT1 gw pw)                      ([x] = [y], x ≠ y)
BAScost.lean:1441 example : BAScostLL gw (gw.BAScost_trA pw) ;  :1443 at gs ([x] ≠ [y])
BAScost.lean:1446 example : BAScostLL gc (gc.BAScost_trB pc qc) := BAScostLL_macroB gc pc qc … gc_same gc_wf1 gc_wf2   (a = 2 ≠ a' = 3, one atom)
BAScost.lean:1454 example : BAScostLL gs (gs.BAScost_trB ps qs)
BAScost.lean:1458 example : ∀ Q ∈ (lanlwT1 gs ps).splitG, BAScostLL gs Q := fun _ hQ => BAScostLL_E2 (BAScostLL_lanlwT1 gs ps ps_mem ⟨rfl, rfl⟩) hQ
BAScost.lean:1473 example : ∃ Q ∈ g2.splitG, BAScostLL g2 Q ∧ Q.sameAtom (inr 0) (inl 1) = true ∧ g2.sameAtom (inr 0) (inl 1) = false ∧ Q.solid.length = 1
BAScost.lean:1479,1482  BReach.step/refl at baPG gs; `induction hQ with | refl | step …`
BAScost.lean:1492 BAScostLL.trans (lanlwT1 then splitG) ; :1502 BAScost_locCostGeA_term at baPG gs, k = 0 (crude bound), partition length 2 (:1506)
BAScost.lean:1511 example : BAInit 2 := baInit_holds 2 ; :1513 partition length 16 ; :1517 a term with locReg6InvA 2, Φ^all ≥ 4, Φ^far ≥ 6
BAScost2.lean ts1_shape, te1_shape, te2_shape, tma_shape, tmb_shape : BAShapeLL sh t at gs, gs, gs, gw, gc (each `h` discharged), applied at k = 0, 0, 0, -4, -4
```
Data: `gs` = `0 → 2 → 1` (2 externals, 1 internal, 3 atoms, 1 waved edge); `gw`, `gc`: 2 externals, 3 internals, an `M`-dotted atom `{2,3}`; `g2`: two parallel uncircled edges. No empty index type, no `False` premise, no large witness; every deterministic hypothesis discharged by `rfl`/`decide`/membership. Every endpoint (Lemma B, E1, E2, S1, macroA, macroB, `baInit_holds`, `BAScost_locCostGeA_term`, the five packed forms) has one. PASS.

## 6. Paper-delta coverage
| difference | candidate |
|---|---|
| macro (a) intermediate = `M`-branch of `lanlw`'s first term; one lemma for `[x] ≠ [y]` and `[x] = [y]` | `T2426a` |
| `E2` has no separate lemma: Lemma B at a split joining two atoms joined by a kept edge | `T2426b` |
| `BReach` a `ReflTransGen` definition, not the pinned inductive | `T2426c` |
Lean-internal (not paper statements, recorded in the prove report (a′)/(d)): Lemma A in "ends in one class" form; packed-form inputs; macroB for blue `q` only. Covered.

## 7. Observations (no RETURN)
- **O1.** Ticket target 5 asks for instances "at the T2397 E13 witness graphs … sharp cases with slack 0". E13 used random parents and names no graph; the Lean instances certify `BAScostLL`, not slack. Slack 0 at `gs` (S1, macroB) and at the macroA graph is shown only by the 1a scripts (prove report (a)(ii)); E2's per-merge slack is ≥ 1 there (min 1 over 346,960 outputs), so no slack-0 E2 instance exists in that measure.
- **O2 (for the dispatcher's planning of L3b4′).** The packed forms leave three inputs open: `BAScostLL P.g X` for the parent builder term of an `e2` output and for macro (b)'s stage-1 terms `d2–d4` (band term lemmas transported to BA, tool `BAScostLL_of_band`), and the stage-2 implication at the packed transfer graph for `macroA`/`macroB`. These are explicit hypotheses, listed in prove report (d)1; no row currently names them as its target. Not a defect of this ticket's statements.
- **O3.** The packed instances `tma_shape`/`tmb_shape` use a step relation whose stage 2 is the identity, so the stage-2 input is discharged by `id`; the data are nondegenerate and the BA-only step is applied.
- **O4.** Prove report: the build line count and claims reproduce; its axiom tally (126 names) differs from mine (185 constants incl. auto-generated `BAShape.*`/structure projections); same three axioms at most.

## Verdict
| target | verdict |
|---|---|
| 1 vocabulary | PASS (BReach equivalent to the pin, compiled; `T2426c`) |
| 2 BA Lemma B with E2 | PASS |
| 3 five shape lemmas (term form; packed forms with explicit inputs) | PASS |
| 4 `BAInit p` | PASS |
| 5 instances | PASS |
| 6 C1 / 7 registry | PASS / none |
**T2426: PASS.** No dispatcher sign-off needed for the merge; O2 is a planning note.
