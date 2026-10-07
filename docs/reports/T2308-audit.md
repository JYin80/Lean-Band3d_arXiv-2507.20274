Auditor model: claude-opus-5-5

# T2308 audit (round 1): BA-P1 `RBM3D/BA/Prop5Short.lean`, `BAProp5s` proved
Written Wed Oct  7 06:00:36 UTC 2026 (`date -u`). Branch `t/T2308` at e0064e5 (merge-base with `main`: ec3f678).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2308-audit1` (detached, e0064e5). The auditor wrote no source.

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2308
 RBM3D/BA/Prop5Short.lean | 814 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   1 -
$ git diff main...t/T2308 -- RBM3D/Test/Axioms.lean   (the only hunk)
-   `RBM.BA.BAProp5s, -- property 5, short form (`prop:ThfadC_short`) for `Θ_BA`: BA-P1 (T2197; T2161 b.2: owed)
```
Only the two sole writable files; Axioms.lean: exactly the owed line deleted, nothing added. No merged file
(`FlowPins`, `MFixedPoint`, `Ward`, `CombesThomas`, `RadialSum`) touched. 814 lines ≤ 1500 (§98 (2)).
Imports of the new file: exactly `RBM3D.BA.FlowPins`, `RBM3D.BA.CombesThomas`, `RBM3D.Defs.RadialSum`.

## 2. Statements against the ticket pins (check file, script-compared, compiled)
Scratch file = check file's imports + `import RBM3D.BA.Prop5Short` + rest of `docs/tickets/checks/T2308-check.lean`
+ 4 `rfl` examples (`T2308Check.X = RBM.BA.X`, X ∈ {BAp5s_A, BAp5s_S, BAp5s_rate, BAp5s_C}) + 13 examples
`example : RBM.BA.T2308Check.Y_pin := @RBM.BA.Y` + `#print axioms` of 13 theorems and 14 instance theorems.
```
$ grep -c '^example : RBM.BA.T2308Check' T2308AuditEq.lean
17
$ lake env lean T2308AuditEq.lean > eq.out; echo "exit $?"
exit 0
$ grep -c error eq.out
0
```
All 4 definitions are definitionally the pinned bodies; all 13 public theorems have exactly the pinned type
(hypotheses, binder order, quantifier order). Pin of the endpoint vs the merged owed pin: `baProp5s_holds (d : ℕ)
(Λ κ : ℝ) : BAProp5s d Λ κ` concludes the merged `BAProp5s` (`FlowPins.lean:182`) verbatim — no primed successor,
no conditional adapter. `C, c` are chosen after `d, Λ, κ` and before `L, g, E, m, t, σ, a` (pin's own order).

Against the paper (`1_2:1146-1150`, `(prop:ThfadC_short)`):
```
$ sed -n 1144,1150p paper/tex/1_2_Intro_model_result.tex | cut -c1-300   (lines 1147-1150 of the output)
Furthermore, when $\sig_1=\sig_2$, we have a much stronger exponential decay: there exist constants $c_\kappa,C_\kappa>0$ (depending on $d$ and $\kappa$) such that
 \big|\Theta^{(\sig_1,\sig_2)}_{t}(0,a)\big|\le C_\kappa \left(1_{a=0} + \ilambda^2 e^{-c_{\kappa}|a|}\right)
In the setting of the block Anderson model, these constants may also depend on $\ilambda^{-1}$ when $1\le \ilambda\le \fd^{-1}$.
```
Lean: both `σ`, `|a| = zdistD`, `C = BAp5s_C d Λ κ`, `c = BAp5s_rate d Λ κ` uniform in `L ≥ 3`, `0 < g ≤ Λ`,
`t ∈ [0,1)` (and `t = 1` in `baProp5s_of_real`), the datum `BAReal` (`κ ≤ Im m`, DECISIONS §51). The `Λ`-dependence
is the dispatcher's §18 reading of `:1150`; it is the merged pin's form, not introduced here. The new statements are
general (no special case): `BApropQ_decay`/`BApropQ_offdiag` are abstract over any `Q` with constant diagonal;
`baProp5s_of_real` is the pin body at one datum with `t ≤ 1` (weaker premise than the pin's `t < 1`).
Unused premises (`t < 1`, `3 ≤ d` beyond `2 ≤ d`) are reported in the prove report and the file header.

## 3. Vacuity, hidden hypotheses, cycles
- No `structure`/`class` is declared in the new file; every theorem's hypotheses are visible in its signature
  (pin types compared in §2). `BApropQ_decay`/`_offdiag` take the row-sum hypothesis explicitly; it is discharged
  for the BA matrix by `BAp5s_row_weighted` (proved here), so `baProp5s_of_real` has only data hypotheses
  (`3 ≤ L`, `2 ≤ d`, `0 < Λ`, `0 < g ≤ Λ`, `0 < κ`, `BAReal`, `0 ≤ t ≤ 1`).
- No external hypothesis is added (none of the 13 theorems takes an owed or unregistered `Prop`).
- Dependencies are merged results only (imports above); no cycle (the new module imports only merged modules; nothing
  merged imports it).
- Hygiene greps on the new file:
```
$ grep -nE "sorry|admit|native_decide|^axiom" RBM3D/BA/Prop5Short.lean | wc -l
0
$ grep -c Matrix.Norms RBM3D/BA/Prop5Short.lean ; grep -c 'seqP\|Prec\|SeqΩ\|Sizes' RBM3D/BA/Prop5Short.lean
0
0
```
- Name clash on current `main` (3c11598), `git grep -l <name> main -- RBM3D | wc -l`:
```
BAp5s_A 0;BAp5s_S 0;BAp5s_rate 0;BAp5s_C 0;BAMss_ss_norm 0;BAMss_ss_diag 0;BAnorm_one_sub_tq_sigma 0;
BAMss_row_offdiag_sum 0;BAMB_sq_off_le 0;BAsum_exp_decay_le 0;BApropQ_decay 0;BApropQ_offdiag 0;
BAp5s_row_weighted 0;baProp5s_of_real 0;baProp5s_holds 0;Prop5sInst 0;BP5_ 0;
```
  Helpers: `private`, prefixed `BP5_` (`BP5_expC_pos`, `BP5_A_pos`, `BP5_S_pos`, `BP5_exp_neg_ge_quarter`,
  `BP5_row_identity`, `BP5_weight_tri`, `BP5_exp_sub_one_le`, `BP5_hyp_row`, `BP5_gap`).

## 4. Compiled nonempty instances (namespace `RBM.BA.Prop5sInst`, `Prop5Short.lean:683-810`)
Data: `d = 3`, `L = 4` (64 sites), `Λ = 10`, merged flow point `P : FlowPt 4 10` (fields `g0_pos : 0 < g0`,
`g0_le : g0 ≤ 10`, `real : BAReal 3 4 g0 (Im m0) E m0`, with `BASelf` giving `0 < Im m0`, `MFixedPoint.lean:193,870-893`),
so `κ = Im m₀ > 0`, `g = P.g0 > 0`: nondegenerate. Every hypothesis is discharged (no open binder):
```
inst_sum_exp_decay      BAsum_exp_decay_le 3 4 _ (1/2) _ 0
inst_ss_norm / _ss_diag / _norm_sigma / _row_offdiag_sum   at P, σ = false/true, rows 0, entry (0,(1,0,0))
inst_sq_off_le          BAMB_sq_off_le 3 4 … 10 P.g0 P.m0.im P.E P.m0 … 0 ![1,0,0] (by decide)
inst_row_weighted       BAp5s_row_weighted … P … (1/2) … false 0
inst_BApropQ_decay      Q = BAMss … true true, q = m0², t = 1/2, ε = (Im m0)²/4, μ = BAp5s_rate 3 10 (Im m0)
inst_BApropQ_offdiag    Q = BAMss … false false, B = A g0², c = BAct_rate, S = BAp5s_S, y = 0 ≠ a = (1,0,0)
inst_of_real_half       baProp5s_of_real at P, t = 1/2, σ = true,  a = ![1,0,0]  (a ≠ 0)
inst_of_real_one        baProp5s_of_real at P, t = 1,   σ = false, a = 0        (endpoint t = 1)
inst_BAProp5s_closed    RBM.BA.FlowPinsInst.inst_BAProp5s (baProp5s_holds 3 10 P.m0.im)
inst_C_pos / inst_rate_pos   at (3, 10, 1/2)
```
The hypotheses of `BApropQ_decay`/`_offdiag` at P are discharged by `BAp5s_row_weighted`, `BAoffDiag_scalar`,
`BAnorm_one_sub_tq_sigma`, `BAMss_ss_diag`, `BAMB_sq_off_le`, `BAsum_exp_decay_le` (lines 732-779), not assumed.
The merged instance `inst_BAProp5s` (`FlowPins.lean:1222`) is closed with no hypothesis left. All compile (§5).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.Prop5Short
✔ [3737/3737] Built RBM3D.BA.Prop5Short (9.7s)
Build completed successfully (3737 jobs).
exit 0
$ grep "depends on axioms" eq.out | head -1; grep "depends on axioms" eq.out | tail -1
'RBM.BA.BAp5s_C_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5sInst.inst_rate_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep "depends on axioms" eq.out | sed 's/^.*: //' | sort | uniq -c
  27 [propext, Classical.choice, Quot.sound]
```
Registry pre-check (copy of the branch's `RBM3D.lean` with `import RBM3D.BA.Prop5Short` inserted after its last
`import` line, as the hub does at merge; `#assert_rbm_axioms` stays last):
```
$ lake env lean precheck.lean > precheck.out; echo "exit $?"
exit 0
$ grep -n "axiom audit:\|registry:" precheck.out | cut -c1-110
1:axiom audit: 8701 theorems, 2844 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
153:registry: 2 borrowed + 143 owed + 105 structural + 7 refuted + 12 superseded; 118 registered premise(s) carr
$ grep -c BAProp5s precheck.out
0
```
Control run (branch `RBM3D.lean` without the new import, `lake build RBM3D`): fails as expected, because
`BAProp5s` is no longer owed while `inst_BAProp5s` still binds it and nothing imported concludes it:
```
error: RBM3D.lean:347:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of …
  [RBM.BA.BAProp5s]
```
So the hub must add the root import at merge (§3 (A) 4) — this is the planned order, not a defect.

## 6. Paper deltas
- Statement differences Lean/paper: none new. The `Λ`-dependence of constants, `BAReal` for `(eq:WO)`/`|E| ≤ e_g−κ`,
  and `zdistD` for `|a|` are properties of the merged pin `BAProp5s` (T2197, DECISIONS §18, §51), unchanged here.
  `baProp5s_of_real` (`t ≤ 1`) and the `(−,−)` case are stronger than / covered by the paper statement.
- Candidate `T2308a` (prove report (d) item 4): the convolution bound at `A:41` holds only with a rate loss;
  numerics pasted there (`d = 1` ratios `a + 2.164`, unbounded). Not used by this route. Proposed, covered.
- Route remark (weighted `ℓ^∞` instead of `(eq:expMLn2)`) listed as a remark, not a delta: correct classification.

## 7. Observations (no RETURN)
- O1. `main` advanced to 3c11598 (T2306/T2307 merged) after the merge-base ec3f678; T2307 may have touched
  `RBM3D/Test/Axioms.lean`. The branch deletes one line only; union rule (§20 (3)) per the ticket.
- O2. Stale docstring `FlowPins.lean:180-181` ("the BA proof is the Taylor expansion") and registry comment
  `Axioms.lean:141`, listed by the prover for the hub; not edited, per §57 (1).

## Verdict
| Target | Verdict |
|---|---|
| 1 constants `BAp5s_A/S/rate/C`, `BAp5s_C_pos`, `BAp5s_rate_pos` | PASS |
| 2–6 `BAMss_ss_norm`, `BAMss_ss_diag`, `BAnorm_one_sub_tq_sigma`, `BAMss_row_offdiag_sum`, `BAMB_sq_off_le`, `BAsum_exp_decay_le` | PASS |
| 7–9 `BApropQ_decay`, `BApropQ_offdiag`, `BAp5s_row_weighted` | PASS |
| 10–11 `baProp5s_of_real`, `baProp5s_holds` (endpoint; merged pin proved unconditionally) | PASS |
| 12 registry (owed line deleted; pre-check green with root import; owed 143) | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
