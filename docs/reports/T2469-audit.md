Auditor model: claude-opus-5-5
# T2469 audit, round 1: L3b2a only (target 1 (a), `RBM3D/Graph/BALocReg2.lean`). Mon Oct 12 21:47:22 UTC 2026
Scope (CONTROL H257 (3), signed split `BALocReg2 | BALocReg2B`): this round audits target 1 (a). Targets 1 (b)-(d), 2, 3, 4 and the `T2469_*` pins belong to L3b2b (`t/T2469b`, `Graph/BALocReg2B`) and are not a defect here. Reserve `BALocReg2C` unused.
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2469-audit1`, detached at `t/T2469` = ff8a75b9. Scratch: `scratchpad/T2469/` (`aparity.py`, `audit.lean`).

## 1. Statement (target 1 (a): no pin in the check file; names not binding; judged against the ticket's mathematics)
Ticket: for each builder term of the T2447 table (17 rows, `T2447-prove.md:9-28`) and `A1` of `gg2`, `BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b` under the constructor's hypotheses and `Γ.Normal`; list forms for `lw2`, `lw4`, the `within` stage-1 list, `gg2`, `gg4`; `ggSplit` `d1`-`d4` (as `BAShapeO2_lw2` ... `_gg4`).
Script: each path lemma against its merged cost twin (`BAShapeO2_*`, `BAScostLL_S1` for `A1`), binder lists compared verbatim and the term `X` (or list) extracted from `BAScostLL Γ X` vs `∀ (k : ℕ) (a b : E), BALocReg1_PathAt Γ k a b → BALocReg1_PathAt X k a b`:
```
$ python3 scratchpad/T2469/aparity.py
BALocReg2_lanlwD       binders =  X =
BALocReg2_withinHead   binders =  X =
BALocReg2_lw2Head      binders =  X =
BALocReg2_lw4Head      binders =  X =
BALocReg2_lw4Tail      binders =  X =
BALocReg2_ggA2         binders =  X =
BALocReg2_ggA3         binders =  X =
BALocReg2_ggA4         binders =  X =
BALocReg2_ggA5         binders =  X =
BALocReg2_ggAD         binders =  X =
BALocReg2_ggB1         binders =  X =
BALocReg2_ggB2         binders =  X =
BALocReg2_ggBD         binders =  X =
BALocReg2_ggSplitD1    binders =  X =
BALocReg2_ggSplitD2    binders =  X =
BALocReg2_ggSplitD3    binders =  X =
BALocReg2_ggSplitD4    binders =  X =
BALocReg2_lw2          binders =  list =  tail_ok True
BALocReg2_lw4          binders =  list =  tail_ok True
BALocReg2_within       binders =  list =  tail_ok True
BALocReg2_gg2          binders =  list =  tail_ok True
BALocReg2_gg4          binders =  list =  tail_ok True
BALocReg2_ggA1         binders =  X =
pairs identical (binders and X/list): 23 of 23
```
Coverage of the T2447 rows: 1 lanlwD, 2 lw2 head, 3 lw4 head, 4 lw4 tail, 5 within head, 6-10 A2-A5, AD, 11-13 B1, B2, BD, 14-17 d1-d4, plus `A1`: all 18 present (declaration list, `BALocReg2.lean:272-660`); the five list forms `:670-733`.
The list forms are stated over the merged builders `Γ.lw2 p`, `Γ.lw4 p`, `Γ.gg2 p q`, `Γ.gg4 p q`, so their terms are fixed by Lean. The `within` list and `d1`-`d4` are written out; against the merged constructor text (`BASim.lean:118-121, 124-137`, with `a = owxEmb 2 p.1.src`, `y = owxEmb 2 p.1.dst`, `y' = owxEmb 2 q.1.src`, `a' = owxEmb 2 q.1.dst`, `dq s md = ext 2 Γ q.2 s [bpW false (bpv 0) (bpv 1)] (bpM a (bpv 0) :: md)`):
```
$ for n in D2 D3 D4; do awk "/^theorem BALocReg2_ggSplit$n /,/:= by/" ... | sed 's/.*BALocReg1_PathAt (/X = (/'; done
X = (BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)])
X = (BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)])
X = (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)])
```
These equal `splitOutsT`'s `dq [bpS true y' (bpv 1)] [bpM (bpv 0) a', bpM (bpv 1) y]`, `dq [bpS true (bpv 1) y] [bpM (bpv 0) a', bpM y' (bpv 1)]`, `dq [] [bpM (bpv 0) a', bpM y' (bpv 1), bpM (bpv 1) y]`; `d1` (`BALocReg2.lean:576-577`) equals `dq [bpS false y' (bpv 1), bpS true (bpv 0) a', bpS false (bpv 1) y] []`; the `within` list (`:690-701`) equals `withinOutsT`'s stage-1 list with `e = bpS true (bpv 1) (bpv 1)`.
Hypotheses: only constructor hypotheses (`hp`, `hq`, `hp1`, `hq1`, `hxy`, `hsame`, `hwf1`, `hwf2`, `hint`), all derivable from the corresponding `BAFrameStepT` constructor (`BASim.lean:139-161`), plus `Γ.Normal`, as the ticket allows. Conclusion `∀ k a b`, stronger than the (non-binding) shape `∀ k` at `(P.ext 0, P.ext 1)` in `T2469-check.lean:295-312` that L3b2b consumes. Some binders are unused (report (b) linter table; paper-delta candidate `T2469b`): this weakens nothing a consumer needs, since the cost twins with the same binders are already discharged in `BAShapeO2B`.
**Verdict 1:** statement matches the ticket's target 1 (a).

## 2. Vacuity, hidden hypotheses, cycles
- No structure, class, `inductive` or `Prop` def is introduced (grep in §4); the predicate `BALocReg1_PathAt` is the merged L3b1 definition (`BALocReg1.lean:65-66`, `localReg2_PathFam` of the atomic image; `localReg2_Fam` `LocalRegular2.lean:147-153` requires an off-diagonal multiset equality with the budget, so it is not trivially true).
- Imports: `RBM3D.Graph.BALocReg1`, `RBM3D.Graph.BAShapeO2`, both on `main` and unchanged by the branch:
```
$ git diff --quiet main...t/T2469 -- RBM3D/Graph/BALocReg1.lean RBM3D/Graph/BAShapeO2.lean RBM3D/Graph/LocalRegular2.lean && echo "imported merged files unchanged"
imported merged files unchanged
$ git show t/T2469:RBM3D/Graph/BALocReg2.lean | grep -nE "open private|^import|^(local )?macro|^syntax"
6:import RBM3D.Graph.BALocReg1
7:import RBM3D.Graph.BAShapeO2
260:local macro "BALocReg2_simp0" : tactic => ...
264:local macro "BALocReg2_msnorm" : tactic => ...
```
- No external hypothesis; nothing from (6), `BAShapeLL`, or the (1)-(5) contract appears in any binder (binder lists = the cost twins' binders, script above). No cycle (new leaf file).
**Verdict 2:** none found.

## 3. Compiled nonempty instances (`BALocReg2.lean:738-882`, in the file, built)
| endpoint | instance | parent invariant (k) | data |
|---|---|---|---|
| `lw2`, `lw4` (lw2Head, lw4Head, lw4Tail, lanlwD) | `:742`, `:862` at `P_W`, `baPL` | `pathInv2_L` (k = 1), satisfied | lists of length 3, 3 (`:879` by `decide`) |
| `within` (withinHead, lanlwD) | `:747`, `:867` at `P_B` | `pathInv2_B` (k = 1), satisfied | `(lwSplit pB.2).length = 2` |
| `gg2`, `gg4` (A1-A5, AD, B1, B2, BD) | `:753`, `:872` at `P_A` | `pathInv2_A` (k = 2), satisfied | lengths 6, 3 |
| `ggSplitD1`-`D4`, `lanlwD` | `:760` at `P_C` | `BALocReg1Inst.pathInv2_C` (k = 2) | see check below |
| `lanlwD` | `:777` at `baPEr` | `BALocReg1Inst.pathInv2_Er` (k = 1) | see check below |
Every constructor hypothesis is discharged (`rfl`, `List.mem_cons_self`, `decide`; `normalEr`), and the premise `BALocReg1_PathAt Γ k 0 1` is a proved theorem at each witness, with `a = 0 ≠ b = 1`. The two `∀ q ∈ lwSplit _` instances are nonempty:
```
$ cat scratchpad/T2469/audit.lean | tail -2
open BASimInst in
example : (lwSplit pC.2).length = 2 ∧ (lwSplit BALocReg1Inst.pEr.2).length = 1 := by decide
$ lake env lean scratchpad/T2469/audit.lean   # (no error lines; exit 0, see §4)
```
No `N = 0`, empty index, collapsed window, `False` premise or huge witness.
**Verdict 3:** present and nondegenerate for every endpoint of target 1 (a).

## 4. Build, axioms, hygiene, diff
```
$ rm .lake/build/lib/lean/RBM3D/Graph/BALocReg2.olean .lake/build/lib/lean/RBM3D/Graph/BALocReg2.trace   # audit worktree only: force a rebuild
$ lake build RBM3D.Graph.BALocReg2 2>&1 | grep -E "^error|BALocReg2|Build completed"
✔ [3829/3829] Built RBM3D.Graph.BALocReg2 (8.9s)
Build completed successfully (3829 jobs).
$ lake env lean scratchpad/T2469/audit.lean | (group by axiom set)   # 39 `#print axioms`: every `theorem` of the file (36 RBM.Graph, 3 BALocReg2Inst)
34 declarations: depends on axioms: [propext, Classical.choice, Quot.sound]
4 declarations: does not depend on any axioms  RBM.Graph.BALocReg2_cends_bpS RBM.Graph.BALocReg2_bpS_σ RBM.Graph.BALocReg2_bpS_src RBM.Graph.BALocReg2_bpS_dst
1 declarations: depends on axioms: [propext, Quot.sound]  RBM.Graph.BALocReg2_cov
exit=0
$ git show t/T2469:RBM3D/Graph/BALocReg2.lean | grep -nE "sorry|admit|native_decide|^axiom|^inductive|^structure|^class|: Prop :=|set_option (maxHeartbeats|debug)"; echo "grep exit=$?"
grep exit=1
$ git diff --stat main...t/T2469
 RBM3D/Graph/BALocReg2.lean | 886 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 886 insertions(+)
$ git diff --name-only main...t/T2469 -- RBM3D.lean RBM3D/Test/Axioms.lean | wc -l
       0
$ git grep -c "BALocReg2" main -- "RBM3D/*.lean" RBM3D.lean | wc -l; git grep -l "BALocReg2[_ ]\|BALocReg2Inst" t/T2470 -- "RBM3D/*.lean" | wc -l
       0
       0
```
Sole writable file touched; 886 lines < stop line 2,000 (reserve rule 1,800 not reached). `RBM3D.lean` import is the hub's at merge. Public helpers carry the stem `BALocReg2_`; instance data under `BALocReg2Inst` (§3 (E), ticket item 5). No frozen signature touched (no merged file in the diff). The full `lake build` is the hub's at merge.
**Verdict 4:** PASS.

## 5. Paper deltas
Lean/paper differences for target 1 (a): the per-term path invariant where the paper asserts it globally (`B_graphical_lemmas.tex:416`), and the binder set (unused constructor hypotheses carried for interface parity), and the A2 selector. Proposed as `T2469a`, `T2469b`, `T2469c` in `T2469-prove.md` (d); none yet in `docs/paper-deltas.md` (`grep -c T2469` = 0), as expected for candidates. Covered.

## Observations (no verdict impact)
- O1. Report (b) says the instance section "starts at line 736"; the `section Inst` line is 738 (the `/-! ## 6 -/` header is 736). Cosmetic.
- O2. The `P_W` instance (`:742`) keeps the parent invariant as a premise; it is discharged at `baPL` (`:862`), so the weight list forms are covered with the invariant satisfied.
- O3. The report's section (a) row 8 central (2,130) and file-1 estimate (1,240) vs the delivered 886 lines: estimate only, recorded in (a′).

## Verdict
Target 1 (a) (L3b2a): **PASS**. No dispatcher sign-off needed. L3b2b (targets 1 (b)-(d), 2, 3, 4) is outside this audit.
