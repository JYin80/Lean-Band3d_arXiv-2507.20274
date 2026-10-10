Auditor model: claude-opus-5-5

# T2391 audit (round 1) — BA-K08b `RBM3D/BA/KSumZeroB.lean`

Time (`date -u`): Sat Oct 10 22:05:18 UTC 2026. Audit worktree `RBM3D-wt/T2391-audit1`, detached at `t/T2391` = `205ffb5`; main = `5ba1ebe`.
Scratch: `$S/T2391` (`S` = session scratchpad).

## 1. Diff, build, axioms, hygiene
```
$ git diff --name-only main...HEAD
RBM3D/BA/KSumZeroB.lean
$ git status --short            # (empty)
$ wc -l RBM3D/BA/KSumZeroB.lean
     755 RBM3D/BA/KSumZeroB.lean          # stop line 2,000
$ lake build RBM3D.BA.KSumZeroB > build.log 2>&1; echo exit=$?
✔ [3774/3774] Built RBM3D.BA.KSumZeroB (4.9s)
Build completed successfully (3774 jobs).
exit=0
$ grep -c "error" build.log ; grep -c "KSumZeroB.lean:" build.log
0
0                                  # 50 warning lines, all in merged upstream files (CouplingWindow, KHeatDiff, GreenSchur, ...)
$ lake env lean ax.lean            # import RBM3D.BA.KSumZeroB; #print axioms x4
'RBM.BA.KSumZeroB_unequal_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_nc_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_weighted' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baSig_sumZeroAbs' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^\s*axiom|set_option (maxHeartbeats|debug)" RBM3D/BA/KSumZeroB.lean | wc -l
0
$ lake env lean docs/tickets/checks/T2391-check.lean 2>&1 | grep -ci error
0
```
`RBM3D.lean` is not touched on the branch (the hub adds the import at merge, §3 (A) step 4). No frozen signature touched (only a new file). Public declarations: the four targets; all other helpers are `private` with stem `KSumZeroB_` (file grep of `^theorem|^private|^def`: 4 public theorems at lines 87, 378, 584, 610; 17 private).

## 2. Statements against the ticket
Pin: the ticket gives the mathematics of B1-B3 and the pin `SigSumZeroAbs d n L g t (BASig d n L g E m t)` for B4, with the hypotheses "`3 ≤ n`, `t i < 1`, `BAReal`, `g i ≤ Λ`" (the family data of K08a's `baSig_signed_sum`, `KSumZeroA.lean:1079`). Binder diff by script (`$S/T2391/stmt.py`, whitespace-normalised, binder lists compared with `baSig_signed_sum`):
```
$ python3 -I stmt.py
baSig_nc_pointwise binders vs baSig_signed_sum: only-new ['(hn : 2 ≤ n)', '(ht1 : ∀ i, t i ≤ 1)'] only-old ['(hn : 3 ≤ n)', '(ht1 : ∀ i, t i < 1)']
baSig_weighted binders vs baSig_signed_sum: only-new ['(Q : ℕ)'] only-old []
baSig_sumZeroAbs binders vs baSig_signed_sum: only-new [] only-old []
  conclusion: SigSumZeroAbs d n L g t (BASig d n L g E m t) | == pin "SigSumZeroAbs d n L g t (BASig d n L g E m t)": True
```
Conclusions (from the file, lines 87-90, 378-383, 584-590):
```
B1  (∃ J : ↥F, β (BAslotIn F J) ≠ β (BAslotOut F J)) ∨ ∃ s s' : BAslot F, s ≠ s' ∧ BAslotNode F s = BAslotNode F s' ∧
      β s ≠ β (BAnextSlot F s) ∧ β s' ≠ β (BAnextSlot F s')            [hyps: KLIsTSP F, 2 ≤ n, leaf labels non-constant]
B2  ∃ G, 0 < G ∧ ∃ c, 0 < c ∧ ∀ i σ δ, (∃ v w, δ v ≠ δ w) → ‖BASig d n L g E m t i σ δ‖ ≤ G * g i ^ 2 * exp (-(c * KLmaxDist δ))
B3  ∃ C, 0 < C ∧ ∀ i σ, (∀ j, σ j ≠ σ (j + 1)) → ∀ r x,
      ∑ δ ∈ univ.filter (δ r = x), ‖BASig … i σ δ‖ * (KLmaxDist δ + 1) ^ Q ≤ C * (g i ^ 2 + (1 - t i))
```
- **B1**: matches the ticket ("a chord with β(In) ≠ β(Out) or a node with two `M`-edges with unequal ends"); hypotheses `KLIsTSP F`, `2 ≤ n` only. PASS.
- **B2**: `∃ G c` precede `∀ i σ δ`: uniform in `(L, g, E, m, t)` as pinned; every `σ`; non-constant `δ`; loss `g²`, decay `e^{-c·maxDist}`. Weaker hypotheses than the sibling (`2 ≤ n`, `t ≤ 1`), i.e. a stronger statement. PASS.
- **B3**: `∀ Q` (outer binder), `∃ C` before `∀ i`, slice `{δ_r = x}`, weight `(maxDist + 1)^Q`, bound `C (g² + (1 − t))`, as the ticket. It is stated for cyclically alternating `σ`, as the blueprint `KLsumZero_weighted` (`KLIndStepA.lean:941-949`) and the pin `SigSumZeroAbs` (`:1042-1046`) are; the ticket's `C_Q` formula appears in the proof's witness (line 597), the statement has `∃ C` as the pin and the band twin do. PASS.
- **B4**: conclusion identical to the pin; hypothesis list identical to `baSig_signed_sum` (the ticket's "`3 ≤ n`, `t i < 1`, `BAReal`, `g i ≤ Λ`" plus the K08a family data `3 ≤ d`, `0 < Λ, κ`, `3 ≤ L i`, `0 < g i`, `0 ≤ t i`). `SigSumZeroAbs` is not edited (T2385 (a+) pin repair). Same ranges as `sigSumZeroAbs_band` (`KLIndStepA.lean:1090`: `3 ≤ d`, `3 ≤ n`). PASS.

## 3. Hidden hypotheses, vacuity, cycles
- No structure carrying hypotheses: every hypothesis is an explicit binder; `BAReal d L g κ E m := BASelf d L g E m ∧ κ ≤ m.im` (`MFixedPoint.lean:432`) is the merged K-family datum, satisfied at the merged flow point `P : FlowPt 4 10` (`MFixedPoint.lean:877-893`, fields `g0_pos`, `g0_le`, `real`).
- Dependencies (all on `main`, the branch diff is one new file): B2 ← `baPure_edge`, `baProp5s_of_real`, `BAK_off_le`, `baSigmaTree_bound`, B1; B3 ← `baSig_signed_sum` (K08a, merged e67bfbd) + B2; B4 ← `baSig_transl` + `baSig_signed_sum` + B3. No cycle (B4 → B3 → B2 → B1 order in the file, lines 87 < 378 < 584 < 610).
- External hypotheses: none (no pin of another gate stays a hypothesis), so no limit check is owed.

## 4. Compiled nonempty instances (all compile: module build above)
Datum: `d = 3`, `L = 4`, `n = 4`, `ι = Unit`, `g = P.g0` (`0 < P.g0 ≤ 10 = Λ`), `κ = P.m0.im`, `E = P.E`, `m = P.m0`, `BAReal` by `P.real`; `δ₀ = (0,0,0,e₁)` non-constant (`⟨0, 3, by decide⟩`, line 639).
```
l.647  B1 at F = {(0,2)} (KLIsTSP by TSP_four; decide), β = Sum.elim δ₀ 0, hn by norm_num
l.653  B1 second disjunct derived (.resolve_left (by decide)): two unequal M-edges of one node
l.665  B2, t = 1/2,      σ = KLsigAlt 4,              δ = δ₀
l.675  B2, t = 999/1000, σ = KLsigAlt 4,              δ = δ₀
l.685  B2, t = 1/2,      σ = (+,+,-,+) (not alternating), δ = δ₀
l.697  B3, t = 1/2,      Q = 4, σ = KLsigAlt 4, slice δ 0 = 0
l.708  B3, t = 999/1000, Q = 4, σ = KLsigAlt 4, slice δ 3 = e₁
l.719  B3, t = 1/2,      Q = 2, σ = !KLsigAlt 4, slice δ 1 = 0
l.730  B4, t = 999/1000: the whole predicate SigSumZeroAbs
l.739  B4 third conjunct at Q = 4 = 2(d-1), t = 1/2, slice δ 0 = 0 (signed and weighted bounds extracted)
```
Every deterministic hypothesis is discharged in the term (`by norm_num` for `3 ≤ d`, `3 ≤ n`/`2 ≤ n`, `0 < 10`, `3 ≤ 4`, `0 ≤ t`, `t < 1`; `P.g0_pos`, `P.g0_le`, `P.real`; `by decide` for alternation). Not `N = 0`, not an empty index, not `t = 0`, not a constant `δ` only, no `False` premise. PASS for every endpoint theorem.

## 5. Paper deltas
Report (d) proposes `T2391a` (weighted form for every `Q` vs the paper's unweighted second estimate of `(eq:Sigma-empty-sum-zero)`, `A:731-734`), `T2391b` (the paper cites rather than proves; BA `g²` source: one unequal short chord or two unequal `M`-edges), `T2391c` (explicit uniform constants; ranges `2 ≤ n`, `t ≤ 1` for B2 and `3 ≤ n`, `t < 1` for B3/B4), and O1 → `T2385b` (`SigSumZeroAbs` has no `n`/`t` range). Every Lean/paper statement difference found in §2 is covered.

## 6. Observations (no verdict effect)
- O-a: B3/B4 use `∃ C` rather than a hard-coded constant (§7 style); the pin `SigSumZeroAbs` and the band twins have this form, and the explicit witness is in the proof (line 597).
- O-b: the restriction of B3 to cyclically alternating `σ` is inherited from the pin `SigSumZeroAbs`; the ticket's B3 text does not mention it. Its paper-delta status belongs to the pin (pre-existing), not to this ticket.
- O-c: `T2385b` is cited as a paper-delta tag but is not yet numbered in `docs/paper-deltas.md` (`grep -n "T2385b\|T2391" docs/paper-deltas.md` → no hits); dispatcher bookkeeping.

## 7. Verdict
| target | verdict |
|---|---|
| B1 `KSumZeroB_unequal_edge` | PASS |
| B2 `baSig_nc_pointwise` | PASS |
| B3 `baSig_weighted` | PASS |
| B4 `baSig_sumZeroAbs` | PASS |
| instances (target 5) | PASS |
| registry (target 6) | PASS (no new Prop-valued premise; `#assert_rbm_axioms` reported in prove report; axioms above standard) |

**T2391: PASS.** No dispatcher sign-off needed.
