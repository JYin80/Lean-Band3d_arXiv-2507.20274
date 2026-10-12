Auditor model: claude-opus-5-5

# T2459 audit (round 1): U5 design gate, BA case (iii) of Step 5. Report-only ticket.
Written Mon Oct 12 17:40:19 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2459-audit1`, detached at `t/T2459` 2a6ad6e. Audited: `docs/reports/T2459-design.md` (the merge deliverable), probe `RBM3D/Probe/T2459Pins.lean` and scripts `docs/reports/T2459/` (they stay on the branch). Scratch outputs: `$S = <scratchpad>/T2459/`.

**Verdict: PASS** (one deliverable: the design report). No dispatcher sign-off is needed from this audit. The dispatcher still has to make the §271 decision that T2460 Amend 1 defers to "after T2459's design report" (O1).

## 1. Diff scope, sizes
```
$ git diff --name-only main...t/T2459 | grep -vE '^(RBM3D/Probe/T2459Pins.lean|docs/reports/T2459-design.md|docs/reports/T2459/)' | wc -l
       0
$ git diff --stat main...t/T2459 | tail -1
 30 files changed, 1704 insertions(+)
$ wc -l docs/reports/T2459-design.md        ->  321 (<= 450)       probe: 394 lines (<= 400)
```

## 2. Probe recompiled, axioms (acceptance script run in the audit worktree, TMPDIR=$S)
```
$ TMPDIR=$S/ bash docs/reports/T2459/probe_check.sh > $S/probe_check.out; diff $S/probe_check.out docs/reports/T2459/out/probe_check.out && echo IDENTICAL
lines:      394
lake env lean RBM3D/Probe/T2459Pins.lean: exit=0, output lines=       0
lake build RBM3D.Probe.T2459Pins: exit=0, last line: Build completed successfully (4065 jobs)., warning/error lines in the probe file: 0
forbidden (sorry|admit|axiom|native_decide|inductive|structure): 0
defs/abbrevs: 26, theorems: 11, examples: 9
T2459_flowFacts_BA / T2459_lam0_le_lam / T2459_kernel_at_flow / T2459_sz0_lam_le / T2459_scalar_sz0 / T2459_main_of_parts /
T2459_Theta_far / T2459_trace_mul_le / T2459_trace_mul3_le / T2459_reg_sz0 / T2459_inst_IngR5: [propext, Classical.choice, Quot.sound]   (11 lines, abridged)
main:0 t/T2450:0 t/T2452:0 t/T2454:0 t/T2455:0 t/T2456:0 t/T2457:0 t/T2458:0 t/T2460:0 t/T2461:0 t/T2462:0 t/T2463:absent
references to T2459Pins or BA/Step5III on main: 0
IDENTICAL
$ TMPDIR=$S/ bash docs/reports/T2459/u6_recheck.sh          # T2458-check Part 2 vs merged Chain/Step5Gen, 11 Iff.rfl
lake env lean exit=0, error lines: 0, warning lines: 0
```

## 3. Numerics reproduced (U5-6), plus the citation and inventory scripts
```
$ for a in exps regime flow "flow big" far hs sums consts shape gron cont; do python3 docs/reports/T2459/num.py $a > $S/out/<a>.out; done; diff -q against docs/reports/T2459/out/
exps: identical  regime: identical  flow: identical  flow_big: identical (rerun; see O5)  far: identical  hs: identical
sums: identical  consts: identical  shape: identical  gron: identical  cont: identical
$ bash cite.sh; python3 cite_lines.py; bash inventory.sh   -> cite: identical  cite_lines: identical  inventory: identical
(cite_lines.out tail: "86 citations, 0 out of range")
```
The key rows (verbatim from `out/flow_big.out`, which reproduces): g = 1/64, `CU=1.0039` at L = 4, 8, 16, 32, 64, 128, `gap(t_b)=0.306`, `ward<=4e-16`. g = 1 (reading g0): `CU` = 1.4795, 1.5053, 1.5158, 1.5163, 1.5163 (L = 4..64). g = 10: `1-t_b>=g0^2:False` in every row, `CU` 1.63 -> 4.01 (L = 4..256). Regime (`out/regime.out`): `window[g]=(0,0.0000]` at g = 1 and 10, `(0,0.6937]` at g = 1/64. None of the constants that the argument uses grows with L or degenerates as t -> t0 where the regime is nonempty.

## 4. Statements (targets and pins) against the ticket
Targets (probe :35-36) against the BA tuple of T2458-check :457-460:
```
check:  T2458_STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0   (same for STPfStep5gL)
probe:  def T2459_STPfStep5BA : Prop := STPfStep5gL 3 (T2459_law 3) (T2459_Flow 3) baFMz BAflowT0
        def T2459_STStep5IIIBA : Prop := STStep5IIIgL 3 (T2459_law 3) (T2459_Flow 3) baFMz BAflowT0
        abbrev T2459_law d := fun sz => Sizes.seqP (sz.withLam 0);  abbrev T2459_Flow d := fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z
```
These match: they are U6's merged names (`Chain/Step5Gen:228, 252`, equal to the check text by `u6_recheck`).
U4s1 copies against `docs/tickets/checks/T2462-check.lean`:
```
$ diff -w <(sed -n 181,187p T2462-check | sed s/T2462_FlowFacts/X/) <(sed -n 39,44p probe | sed s/T2459u4_FlowFacts/X/)
7d6  <  (blank line only)
T2462-check:225-226  T2462_FlowFacts d Flow mk T0 → STPfStep5gL d law Flow mk T0 → STStep5IIIgL d law Flow mk T0   = probe :49
```
Kernel pins (`T2459_BAweighted` :69, `T2459_BAKernel` :78), UBA-C4 reading. The hypotheses are `0 < lam0 n`, `lam0 n ≤ 𝔡⁻¹`, `lam0 n ≤ sz.lam n` (the kernel at g0 ≤ g), `sz.lam n ^ 2 ≤ 1 - t` (the regime at g = `sz.lam`), and `∃ Cc` after `∀ κ 𝔡`. The conclusion is merged `STTailtoTailConclgL` (`Step5Gen:169`: `Cc·T_t + ((1-s)/(1-t))²W^{-D}`). I checked the inputs against their merged signatures:
- `BAK_off_le` (`KKernel:197-200`) needs `3 ≤ L`, `0 < g ≤ Λ`, `BAReal`. `Sizes.three_le_L` is a field (`Defs/Sizes:145`), so this is no hidden hypothesis.
- `TwistStep2_lam0_sq` (`TwistStep2:740`): conjunct 1 is `g0² ≤ g²` (the only one read); conjunct 2 is `g² ≤ (κ+1)/κ g0²`, which does not enter. The C1 table row "regime | first conjunct only | not entered" is correct.
- I redid the BA row-sum identity by hand: `Σ_b U_ab = s/t + (1-s/t)/(1-t) = (1-s)/(1-t) = ρ`. So the floor `ρ² W^{-D}` comes with coefficient exactly 1, as in the U6 conclusion. With `τ_s ρ = τ_t`, the step `Cc = (3e^{1/(4μ)})²` is consistent.
- C1-forbidden facts, `grep -cE 'BAK_le_small|BAMB_upper_small|BAGbEXPij[^']|Mbound_AO|W\^\(-eps|BAm_im_lower_window'` on the probe: **0**. No `g ≤ W^{-ε}` and no `‖M - m₀I‖` smallness.

ℰ-bounds (`T2459_BAscalar` :107, `T2459_BAmatrix` :116, `T2459_BAEdet` :134):
- Every parameter its loss uses is in the signature (`Λ K₀ J θ Cd D u`, `lossE2wG d L W Λ K₀`), as TEAM lesson 10 requires.
- Ingredient (vi) interpolates `STLKU` (k = 2) with `STGdecayWgL` (`Step2Gen:503`: `ρ^Cd Bctl^{1/5} STWB e^{-√(r/ℓ)} + W^{-D}`; `STWB = W^{-d} Bparam`, `Induction/Defs:69`). The exponent count `A2/A1 ≤ C W^{d(Cd+1)}` checks: `ρ ≤ λ^{-2} ≤ W^d`, `τ ≥ W^{-d}`.
- The `dif` factor `W^{2θd(Cd+1)} Σ_y e^{-(θ/2)√|y|}` is proposed as T2459f.

U5-1 to U5-3 are derived by hand at paper level. The report says so (f): the hand derivations are not compiled. That is the norm for a design gate. Compiled are the merged-name theorems `T2459_Theta_far`, `T2459_flowFacts_BA` and the Hilbert–Schmidt bounds.

## 5. Vacuity, hidden hypotheses, cycles
- No `structure` in the probe (grep 0). All pins are `def … : Prop` over merged names.
- The probe theorems use merged names only (they compile on main's base 1debc23). Unmerged inputs enter as hypotheses of exact type: `T2459_P1` (`STGridRepNAtgL 3 2` at `baStep2Mat`), `T2459_caseIII_succ` (T2462 target 4), `T2459u4_FlowFacts`.
- There is no cycle: `T2459_BAclosure : P1 → Kernel → Edet → goodThm → Walk` is a hypothesis-only pin, and `T2459_main_of_parts` derives the target from `Walk` and `fromWalk`.
- `T2459_flowFacts_BA` discharges U4s1's premise at BA by merged names (`h.1`, `EMn2BA_T0_lt_one`, `BAflow_real`, `rfl`). The step `STStep5IIIgL` from `STPfStep5gL` is therefore one line (example :342).

## 6. Compiled nonvacuous d = 3 instances (`sz0`, `zSeq`, `flow_sz0`, s ≡ 1/10 < t ≡ 1/2 < t0)
| pin | instance (probe line) | deterministic hypotheses | left as hypotheses |
|---|---|---|---|
| `T2459_STPfStep5BA` | :338 via `T2459_inst_IngR5` :328 | flow, window (`half_lt_t0`), regime `T2459_reg_sz0`, `(con_st_ind)` `s1Setup_conStInd_const`: discharged | the target itself; `T2459_prem` = Steps 1-4 pins (other gates) |
| `T2459_STStep5IIIBA` | :342 | `T2459_flowFacts_BA` (proved) | T2462 target 4 (unmerged row) |
| `T2459_BAweighted`, `T2459_BAKernel` | :346, :357 | `BAflow_real`, `BAflow_lam0_window`, `T2459_lam0_le_lam`, regime: discharged | the pin |
| `T2459_BAscalar` | `T2459_scalar_sz0` :154 (n = 1, L = 8, W = 1024, u = 1/2, D = 40) | proved | none |
| `T2459_BAEdet` | :364 | scalar part proved | the pin; `T2459_BAmatrix` (O2) |
| `T2459_BAgood(Thm)` | :373 | all discharged | Steps 1-4 pins |
| `T2459_BAWalk`, `T2459_BAfromWalk` | :379 | all discharged | the pins; `T2459_prem` |
| `T2459_Theta_far` (theorem) | :384 (t ≡ 1/2, D = 1) | all discharged | none |
| `T2459_P1` | none | n/a | an unmerged row's pin, of exact type (ticket U5-7 (iv)) |
No instance uses `N = 0`, an empty index set, a collapsed window or a `False` premise: `sz0` has `L = 4(n+1) ≥ 4` and `W = (2(n+1))^5`.

## 7. Binding CONTROL items
- **H249 (3)** (design :192): the answer is "No". Clause (iv) has one frozen twist; slot 2 is a source, and closing it by Gronwall loses `((1-s)/(1-t))^{C_ell-1}`. `out/gron.out` reproduces: loss 1.001 at `1-u = 1/2` and `5.19e+07` at `1-u = 2.441e-04`. The report labels the argument as a sketch with proxy numerics, and it states that the summation-by-parts outline has the same unchecked cross-twist QV step. The question is answered, conservatively. See O1 for how it interacts with T2460 Amend 1.
- **H250 (3), UBA-C4**: line 1, (a) regime, and the U5-5 table (column "the A of UBA-C1"). The kernel is read at g0 ≤ g, the regime at g = `sz.lam`, and A = (κ+1)/κ is "not entered". This is confirmed by the pin signatures (§4).
- **H250 (4)** fill-in table, design :274-321:
```
$ awk 'NR>=276&&NR<=321' design.md | awk -F'|' '{gsub(/ /,"",$3); if($3=="")e++; n++} END{print n, e+0}'   ->  46 rows, 0 empty "where" cells
```
  I spot-checked the section references: (a) 6, (b) 132, U5-0 135, U5-1 163, U5-2 172, U5-3 184, H249 192, U5-4 194, U5-5 197, (c) 210, (d) 250, (e) 262, (f) 270. They agree with `sed -n <L>p`. The U5-7 (i) row ("n/a, because U6 is merged 1debc23") is correct: `git merge-base --is-ancestor 1debc23 t/T2459` holds, and the re-check is in §2.
- First line of the design report: it gives the verdict ("CLOSES WITH NAMED INPUTS"), the regime reading, and the rows and central (5 rows, central 6,900; lo 4,650 / hi 10,600), as required.

## 8. Paper deltas
`T2459a` (ready-to-paste: what `7_8:2100-2103` omits, kernel / ℰ / closure, inputs, regime) and `T2459b`–`f` are in design (e). I checked the paper text: `sed -n 2099p paper/tex/7_8_light_weight.tex` is "The proofs in … extend verbatim to the block Anderson model, except for the arguments in \Cref{sec:Step5_larget} …".
Every Lean/paper difference found is covered:
- the regime reading (a);
- the thresholds `2ℓ*`, `6ℓ*` (b);
- no `lem_GbEXP_BA` used (c);
- the free-`lam0` shape (d);
- the Θ-level far field (e);
- the `dif` factor (f).

`docs/paper-deltas.md:1598` already lists T2459a as a pending candidate.

## 9. Observations (non-blocking; none changes a statement, instance, build, axiom or delta coverage)
- **O1 (for the dispatcher, §271): the producer list is stale.** Design (d) says "Inputs with no producer: none (P1: T2460, released H249)". But T2460 Amend 1 (committed a1628b9, 17:13 UTC, before the report) says "Target 4 … leaves this row before 1b … decided after T2459's design report", and `docs/queue/T2460.state` reads "1b prover-hard without target 4". With this report's answer "No", P1 clause 4 at `baStep2Mat` has no producer until the dispatcher either puts target 4 back in T2460 or opens a two-slot BA-tail T row. Amend 1 already reserves that decision for the dispatcher, so this audit does not ask for a separate sign-off.
- **O2: the matrix part of `T2459_BAmatrix` has no witness.** The `T2459_BAEdet` example (:364) keeps it as a hypothesis, at `Λ = K₀ = J = 1`, n = 1. Its satisfiability at that data is not shown: the stopped control (i) with J = 1 is a concentration bound at precision τ². I accept it under the "other gate's pin" allowance:
  - `T2459_BAmatrix` is exactly the ω-wise content of U5c's `T2459_BAgood`;
  - `T2459_BAgoodThm` (whose instance :373 discharges all deterministic hypotheses) implies that it holds on an event of probability ≥ 1 - N^{-D₁}, so it is satisfiable eventually.

  Recommendation for U5b/U5c's 1b: the ℰ-bounds instance should take `hmat` from `T2459_BAgood` (ω ∈ G, Λ = K₀ = N^{τ'}, J = J♯), not leave it as a free hypothesis. The compiled chain also does not check that BAgood's output parameters meet `T2459_BAscalar` (`J ≤ W^{1/2}` comes from the stopped event).
- **O3: the free-`lam0` shape (U5-1 "also answer").** The ticket asked for "a proof or a numeric counterexample". The report gives neither: it offers a continuum Yukawa argument (`out/cont.out`) and lattice numerics that cannot decide (they would need L ≥ 18,365). The heuristic is sound in outline. In the shape, Cc may depend on `lam0` and κ, and the test datum `A = τ₀²δ` forces `((1-t)Θ)² ≤ Cc e^{-√(2|x|)}`, which fails at `R ≈ ℓ²/8` as ℓ → ∞. U5 does not consume the shape (dispatcher note (4)), and T2459d says "expected".
- **O4: g = 10 `CU` growth (1.63 -> 4.01).** Not a stop. In every g = 10 row `1-t_b>=g0^2:False`, so these data lie outside the hypothesis `g0² ≤ 1 - t` of the kernel argument, and the regime is empty under both readings. No constant of the argument is evaluated there.
- **O5: one failed run of `flow big`.** The first `num.py flow big` run in my loop exited 1 with no output kept. A rerun with stderr captured exited 0 (numpy overflow `RuntimeWarning` only) and is identical to `out/flow_big.out`.
- **O6: the drafting count is not reproduced.** The ticket's count of 23 for `|E| < 2` is not reproduced (17 literal, 59 with `≤`). The report says so (F9); my `inventory.sh` run is identical.

## 10. Per-target verdict
| target / deliverable | verdict |
|---|---|
| `docs/reports/T2459-design.md` (report-only merge) | PASS |
| BA target `STPfStep5gL` at `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, design pin and argument | PASS (design level; pins compile with instances) |
| BA target `STStep5IIIgL`, one line through T2462 target 4 | PASS |
| Probe `RBM3D/Probe/T2459Pins.lean` (stays on the branch) | PASS (exit 0, standard axioms, 394 lines) |
