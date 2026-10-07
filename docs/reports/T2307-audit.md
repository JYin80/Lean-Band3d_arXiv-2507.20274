Auditor model: claude-opus-5-5

# T2307 (LW-14e-2) audit, round 1 — Tue Oct  6 15:27 UTC 2026

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2307-audit1` (detached at `t/T2307` = 90f1a30, base 4686e08). Scratch: `scratchpad/T2307/audit/`.

## 1. Diff scope, build, axioms
```
$ git diff --name-only main...t/T2307
RBM3D/Graph/LWExpTerm5.lean
$ lake build RBM3D.Graph.LWExpTerm5 | grep -E "error|Build completed"    # olean rebuilt 15:22 UTC (not in the copied cache)
Build completed successfully (3882 jobs).
$ lake build | grep -E "error|Build completed"
Build completed successfully (4111 jobs).
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Graph/LWExpTerm5.lean | wc -l
       0
$ lake env lean ax.lean     # #print axioms
'RBM.Gauss.Sizes.lwExpandIdentity_holds' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expandG_sum' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expand_eq_expandG' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.RCand.kids_identity' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.RCand.kids_normal' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.val_eq_partitionX' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.partitionX_spec' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.partitionX_normal' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwSplitLoopsX_spec' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.oe2xR1_val_zero' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.lwG5Cand_iff_nonempty' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_identity' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_kids_identity' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_R1_val_zero' [propext, Classical.choice, Quot.sound]
'RBM.Gauss.LWInst.lwExpTerm5_inst_val_eq_partitionX' [propext, Classical.choice, Quot.sound]
exit 0
```
Imports (file lines 6-15): exactly the ten modules the ticket lists; no `RBM3D`, `Probe.*`, `LWExpCert*`.

## 2. Statements against the pins
Normalised text diff (`blk.py`: declaration header+body, whitespace collapsed, `Pin` stripped; docstrings excluded).
```
$ python3 blk.py docs/tickets/checks/T2307-check.lean LWExpTerm5.lean LWJoined,...,ExpandGSum   # check-file §2
LWJoined: SAME  LWG5Cand: SAME  LWG5Progress: SAME  LWG5Identity: SAME  lwSplitLoopsX: SAME
RCand: SAME  Sel: SAME  expandG: SAME  ExpandGSum: SAME
$ python3 blk.py probe.lean LWExpTerm5.lean ...    # probe = git show t/T2288:RBM3D/Probe/T2288Cert.lean (5f3d37f)
LWJoined: SAME  LWG5Cand: SAME  LWG5Progress: SAME  LWG5Identity: SAME  lwSplitLoopsX: SAME
partitionX: SAME  PartitionXSpec: SAME  pcomp: SAME  RCand: SAME  lwG5Cand_iff_nonempty: SAME
RCand.kids: SAME  Sel: SAME  expand: SAME  expandRoot: SAME  LWExpandIdentity: SAME
selClassical: SAME  lwSplitLoopsX_spec: SAME
$ python3 tk.py     # headers up to `:=` against the ticket's Targets 3-5 texts
lwStep SAME  expand_eq_expandG SAME  val_eq_partitionX SAME  partitionX_normal SAME
RCand.kids_normal SAME  RCand.kids_identity SAME  lwExpandIdentity_holds SAME
partitionX_spec DIFF   (script artefact: the regex stops at the `:=` inside `(E := E)`;
                        file line 310 reads `theorem partitionX_spec : PartitionXSpec (E := E) (I := I) := by`)
$ sed -n 261p LWExpTerm5.lean      # lwStep body = ticket text
  if (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder then none else (sel P).map RCand.kids
```
Lean check of check-file §2 (lines 99-190 copied verbatim into `RBM.Gauss.Sizes.T2307Check`, importing `RBM3D.Graph.LWExpTerm5`):
```
a_joined/a_cand/a_prog/a_id : Pin ↔ name := Iff.rfl            (all four elaborate)
a_split : lwSplitLoopsXPin es = lwSplitLoopsX es               (induction; simp only [.., ih])
a_expG  : expandGPin st n P = expandG st n P                   (induction on n; cases st P)
a_sum   : ExpandGSumPin st Inv Φ w ↔ ExpandGSum st Inv Φ w      (unfold; simp only [a_expG])
a_main  : ∀ (sel : Sel) (fuel : ℕ), LWExpandIdentity sel fuel := @lwExpandIdentity_holds
a_sumthm: ExpandGSumPin st Inv Φ w := (a_sum ..).2 (expandG_sum ..)
$ lake env lean pin.lean
'..T2307Check.a_split' depends on axioms: [propext]
'..T2307Check.a_expG' depends on axioms: [propext, Quot.sound]
'..T2307Check.a_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'..T2307Check.a_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'..T2307Check.a_sumthm' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
`oe2xR1_val_zero` (ticket: "`Γ.Normal` plus whatever the preflight finds necessary; say so"): file line 364 takes `hN : Γ.Normal`, `hp : p ∈ lwSplit Γ.solid`, `hy : y ≠ Sum.inr x`, `hp1 : p.1 = ⟨true,false,Sum.inr x,y⟩` — exactly the hypotheses of `oe2xR1`/`oe2x_graph_E`'s candidate data, all supplied by `RCand` fields in `kids_identity` (line 543); nothing extra. Merged analogue binders: `LGraph.val_eq_partition (m) (Γ) (D) (hM : ∀ x, D.M x x = m) (ℓe)` (`LWVocab:1339`, `ι` from `variable` at 1205) — `val_eq_partitionX` has the same order.

Quantifiers/ranges: `LWG5Identity` (pinned, verbatim) fixes `sz n E t` before `k s x y`, `|E|<2`, `0<t<1`; `expandRoot` does not see `sz,n,E,t,x,y` (§29 (5)); `lwExpandIdentity_holds` holds for every `sel` and every `fuel` (the general target, not a special case). `kids_identity`: all seven families `R2..R8` appear with shifts 3/1/3/1/3/(1,3 over `lwSplit c.q.2`) as in the probe's `RCand.kids` (verbatim); `R1` removed via `oe2xR1_val_zero` inside the proof (line 542-545), not by a hypothesis.
**Statement verdict: all targets 1-5 match the pins.**

## 3. Vacuity, hidden hypotheses, cycles
- No theorem takes an owed `Prop` or a structure with a proof obligation as hypothesis. `RCand` fields (`hp,hq,hy,hy',hp1,hq1`) are the pinned candidate data (verbatim from probe/check file) and are inhabited at concrete data (`lwExpTerm5_instCand`, lines 651-671, fields closed by `simp`/`rfl`).
- `kids_identity` uses `oe2x_graph_E` (merged, `LWGGExp:1550`) with every hypothesis discharged by merged lemmas (lines 520-522: `gaussIBP sz`, `lwWx_im_pos`, `ht0`, `lwWx_mE_ne`, `lwWx_flow`, `lwSplus_spec`, `hM` by `simp`); integrability from `lwStein_term_tame1`/`Tame.integrable` (line 426). No external hypothesis enters, so no limit check is owed.
- Dependencies are merged modules only (imports above); no reference to downstream names; axioms standard ⇒ no cycle, no hidden hypothesis.
- Registry pre-check (ticket acceptance):
```
$ printf 'import RBM3D\nimport RBM3D.Graph.LWExpTerm5\n#assert_rbm_axioms\n' > reg.lean; lake env lean reg.lean > reg.out; echo $?
exit 0
$ head -1 reg.out
axiom audit: 8675 theorems, 2854 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -cE "LWJoined|LWG5Cand|LWG5Progress|LWG5Identity|PartitionXSpec|LWExpandIdentity|ExpandGSum|LWExpTerm5" reg.out
0
```
The pre-check lists none of the new `Prop`s, so the ticket's rule "add only what the pre-check lists" requires no `Test/Axioms.lean` edit; none was made (diff scope above).

## 4. Compiled nonempty instances (file `RBM.Gauss.LWInst`, all compiled in the module build)
| endpoint | instance (line) | data | hypotheses left |
|---|---|---|---|
| `lwExpandIdentity_holds` | `lwExpTerm5_inst_identity` (637) | `d=3`, `sz0` (`L 0 = 4`, `W 0 = 32`, `Sizes.lean:260-262`), `n=0`, `E=STflowE z0 0`, `t=1/16`, `selClassical`, fuel 4, all `k s x y` | none (`abs_lemE_lt_two (z0_im_pos 0)`, `norm_num` ×2) |
| `RCand.kids_identity` | `lwExpTerm5_inst_kids_identity` (676) | same data; `lwExpTerm3_instGraph` (5 solid, 2 waved, 3 dotted edges, `LWExpTerm3:2191`), candidate `x=α`, `p=G_{αy}`, `q=G_{xα}` | none (`lwExpTerm3_instGraph_normal`) |
| `RCand.kids_normal` | `lwExpTerm5_inst_kids_normal` (684) | same candidate | none |
| `oe2xR1_val_zero` | `lwExpTerm5_inst_R1_val_zero` (688) | same graph/candidate, all `m D ℓe` | none |
| `val_eq_partitionX` | `lwExpTerm5_inst_val_eq_partitionX` (695) | `LWG5Graph k s`, `LWG5Data sz0 0 ..`, every `ω x y` | none (`hM` by `lwExpTerm3_Data_M`) |
| `partitionX_spec`, `partitionX_normal` | examples 703, 704 | `E=Fin 2, I=Fin 3`; `LWG5Graph k s` | none |
| `lwSplitLoopsX_spec` | examples 705, 710 | 3-edge list, `length = 4` by `decide` | none |
| `expand_eq_expandG` | example 714 | `selClassical`, fuel 4, root `(LWG5Graph false false).pack` | none |
| `expandG_sum` | example 719 | step on `ℕ` branching twice below 2, fuel 2, `w=(1/2)^(a+b)`, `Φ=1` | none; conclusion `1 = Σ` over 4 leaves |
No `N=0`, empty index, collapsed window or `False` premise; `sz0` gives `N = (4·32)^3 = 2097152`.

## 5. Paper deltas
Lean vs paper (`B:78-94`, `7_8:334-349`): (i) coefficients tracked as `m^j m̄^{j'}` (red/conjugate weights) — covered by candidate T2265b (`docs/reports/T2265-prove.md:182`); (ii) partition merges internal vertices with `x,y` — T2265a (`:181`); (iii) order/depth facts — T2288a–e (D612, `docs/paper-deltas.md:1571`); (iv) the `mδ_{xy}` term (`R1`) is dropped by value on normal graphs (the `×`-edge on `{x,y}` forced by `Normal`), consistent with `dot-def`'s `≠` convention, not a statement difference; (v) identity for every `sel`/`fuel` is stronger than the paper needs (ticket: no delta). Prove report (d) proposes none beyond these; coverage complete.

## 6. Observations (no verdict impact)
1. T2265a–c exist only as candidates in the withdrawn T2265's report (`grep -c "T2265[a-c]" docs/paper-deltas.md` = 0); the dispatcher may want to number them when T2265's material is closed.
2. Branch base is 4686e08; `main` is now 4db5994 (T2305 merged). `git grep` on `main` for the new public names (outside `Probe`) returns 0 hits; the hub's merge-time full build covers the rest.
3. `Test/Axioms.lean`: the ticket "expected" `LWJoined`, `LWG5Cand`, `LWG5Progress` in `structuralProps`, but the pre-check does not list them (no theorem takes them as hypotheses); prover and auditor runs agree (exit 0, no listing).

## Verdict
| target | verdict |
|---|---|
| 1 vocabulary `LWJoined`, `LWG5Cand`, `LWG5Progress`, `LWG5Identity` | PASS |
| 2 procedure `lwSplitLoopsX`, `partitionX`, `PartitionXSpec`, `pcomp`, `RCand`, `lwG5Cand_iff_nonempty`, `RCand.kids`, `Sel`, `expand`, `expandRoot`, `LWExpandIdentity`, `selClassical` | PASS |
| 3 `expandG`, `ExpandGSum`, `expandG_sum`, `lwStep`, `expand_eq_expandG` | PASS |
| 4 `lwSplitLoopsX_spec`, `partitionX_spec`, `val_eq_partitionX`, `partitionX_normal`, `oe2xR1_val_zero`, `RCand.kids_normal`, `RCand.kids_identity` | PASS |
| 5 `lwExpandIdentity_holds` | PASS |
| 6 instance `lwExpTerm5_inst_identity` | PASS |

**T2307: PASS.** No dispatcher sign-off needed.
