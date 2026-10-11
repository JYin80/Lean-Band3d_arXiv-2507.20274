Auditor model: claude-opus-5-5

# T2413 audit (round 2): BA TL-D, design of stage TL (report-only ticket)

Written Sun Oct 11 10:19 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2413-audit2`, detached at `t/T2413` = `76c586e`.
Inputs: ticket `docs/tickets/T2413.md`, `docs/reports/T2413-prove.md` (with "Repair (audit round 1)"), `docs/reports/T2413-design.md` (112 lines),
probe `RBM3D/Probe/T2413Pins.lean` (387 lines), round-1 audit (its RETURN list), `t/T2398` at `6429bb5`.

**Verdict: PASS.** Both round-1 RETURN items are repaired. No other statement changed (repair diff below). No dispatcher sign-off is needed for this audit.
The >8-row REQ is the dispatcher's standing step under 0853 TLS Q1, and the design's first line flags it.

## 1. Build, hygiene, diff
```
$ lake build RBM3D.Probe.T2413Pins 2>&1 | grep -E "T2413|error|Build completed"; echo exit=$?
Build completed successfully (3997 jobs).
exit=0                                  (no error or warning line in the probe; other lines are warnings of merged files)
$ lake env lean RBM3D/Probe/T2413Pins.lean          -> exit 0, no error line
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2413Pins.lean | wc -l
       0
$ git diff --stat main...HEAD
 RBM3D/Probe/T2413Pins.lean | 387 +++++++++++++++++++++++++++++++++++++++++++++
$ wc -l RBM3D/Probe/T2413Pins.lean docs/reports/T2413-design.md
     387 RBM3D/Probe/T2413Pins.lean   (stop size 400)
     112 docs/reports/T2413-design.md (stop size 300)
$ grep -c "Step2Gen_\|STthetaOpg" RBM3D/Probe/T2413Pins.lean      # BAT-F1: no generic kernels
0
```
The design report is in the main worktree (untracked), as in round 1. The hub commits it at the report-only merge. Observation only.

## 2. Axioms
My script copies the probe to a scratch module, renames every `example` to `noncomputable def auditExNN`, and appends `#print axioms`:
```
$ lake env lean RBM3D/Probe/AuditAx2413.lean > ax.out; echo exit=$?      (scratch file removed afterwards)
exit=0
$ grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out
24          (auditEx01..auditEx20, twTr_eq, twMB_ba, twK_ba, twFrame_inst)
$ grep axioms ax.out | grep -v "\[propext, Classical.choice, Quot.sound\]"
(no output)
```

## 3. Verbatim copy from `t/T2398:RBM3D/Probe/T2398Pins.lean` at `6429bb5` (declaration blocks, my `verb.py`)
```
twBlk old:203 new:43 identical:True      twShift old:208 new:47 True     twTr old:213 new:51 True     twChg old:281 new:57 True
twTrP old:284 new:59 True                twLoopX old:288 new:62 True     twTr_eq old:295 new:64 True  twL2' old:298 new:66 True
twMB old:302 new:69 True                 twK old:306 new:72 True         twMB_ba old:311 new:76 True  BATwistAvgLaw old:323 new:87 True
BATwistLoopLaw old:328 new:91 True       twSq old:336 new:96 True        twFold old:340 new:99 True   twWard old:345 new:103 True
twCirc old:352 new:109 True              twK_bound old:360 new:116 True
$ diff <(sed -n 276,278p old) <(sed -n 53,55p new) && echo identical     # convention docstring
identical
```

## 4. Repair diff `fcdfdc0..76c586e` (the only change since round 1)
```
$ git diff fcdfdc0 76c586e --stat
 RBM3D/Probe/T2413Pins.lean | 20 ++++++++++++--------
 def BAChainTL (d : ℕ) : Prop :=
   BAMainIndTL d STAny → STHorizonG d (...) (...) →
-    STBaseG d (...) (...) baFMz → BATwistLoopBase d → BAMLOutTL d
+    STBaseG d (...) (...) baFMz → BATwistLoopBase d →
+      (∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) → BAMLOutTL d
 example 11: + (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) : BAMLOutTL 3 := h hm hh hb ht hG
 example 19 (T.10 (d)): (v, u) = (1 - g₀²/L², 1 - g₀²/L²)  ->  (1 - Pf.g0^2/16, 1 - Pf.g0^2/32), with `v < u` in the conclusion
```
The other declarations (lines 1-176 and the rest) are unchanged, so the round-1 PASS findings on them still hold. They are re-checked briefly in §5.

## 5. Statements (per target)

**D6, TL-V pin `BAChainTL` (probe 179): PASS (round-1 defect repaired).**
- The new premise has the form of the merged `Induction/MainIndBase.lean:157` (`hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow ... → STG0M (baFMz sz z)`).
- `STG0M` is `∀ n ω x y, C.G n 0 ω x y = C.M n x y` (`MainIndBase.lean:54-55`). It is an owed pin of another gate: `Test/Axioms.lean:139`, "BA: BA-V `GLoopAtT0`".
- TL2 at `0` now comes from `BATwistLoopBase d` with this premise. The six conclusions at `0` come from `STBaseG` (`MainIndBase.lean:58-61`: `STConclgL ... (fun _ => 0)`).
- The step comes from `BAMainIndTL`, and the horizon from `STHorizonG`. With these, every input of the chain twin of `stPosConclG_of_mainIndG` is among the premises, and none is hidden in a structure field.
- Design §6 (line 84) now says "This part needs merged files plus two hypotheses: the step `BAMainIndTL`, and `G_0 = M` at the carrier ... which BA-V `GLoopAtT0` owes".
- §7 (line 101) says "TL-V takes `STG0M` at `baFMz` (BA-V `GLoopAtT0`) as a premise of `BAChainTL`; a consumer that discharges `BAChainTL`'s premises ... needs BA-V `GLoopAtT0` merged first". Both corrections asked in round 1 are made.
- Non-vacuity: the premise asserts the carrier identity `G_0 = M`. The band analogue `lwExpTerm3_Gt_zero` is merged (`Axioms.lean:139`), and BA-V owes the BA form. It is not a `False` premise.

**D2, T.10 (d) `BATwKerZero` (203): PASS. The instance is now nondegenerate (example 19, probe 371-378).**
At `Pf` (`L = 4`, `0 < g₀ ≤ 1/2`), `A = 1`, `v = 1 − g₀²/16`, `u = 1 − g₀²/32`, the hypotheses are discharged in the proof:
- `0 ≤ v` (`nlinarith`, `g₀² ≤ 1/4`);
- `(1−v)L² = g₀² ≤ 1·g₀²` (`norm_num`);
- `v ≤ u` and `u < 1` (`linarith`, `g₀² > 0`).

The example also proves `v < u`, so the window is not collapsed. It compiles (§1, §2).

**Unchanged targets (round-1 PASS re-confirmed on the same text):**
- `BATwistAvgProd` (148): T.7. Premises `LWAvgLawgL` and `STLmaxgL` at `t`; conclusion the verbatim `BATwistAvgLaw`.
- `BATwistLoopStep` (154) in `BATwFrame` (140): T.12′. Hypotheses: `twSteps` on `[s,t]` (`STStep2ConclgL`, (2.89), (2.90), Claim 4.5), `STConStInd 𝔠d s t`, and (e_s). Conclusion: TL2 for every `τ` with `s ≤ τ ≤ t`, per `τ`. Quantifiers: `∀ κ ε 𝔡, ∀ Cd > 0, ∃ 𝔠d ∈ (0,1/100], ∀ 𝔠 sz z`.
- `BATwistLoopBase` (158): the base case.
- `BAMainIndTL` (163): `STMainIndG` at BA, plus the fifth hypothesis, the fifth conclusion and the regime `R`.
- `BAMLOutTL` (172).
- `BATwKerA`, `BATwKerFar` (187, 193), and T.10 (c) = merged `baEKSameRow_holds`.
- `BATwistZeroMode` (211, T.12″).
- `BATwistSrc1`-`BATwistSrc5` (255-270, T.11 (i)-(v)): BA kernels only, via `twK_ba` (273), which is `BATheta`/`BAMsigma`/`BAMB`.
- D3 (`twK_bound` verbatim; O2 `∃ C(d,κ,ε,𝔡)`; O3 = example 12, `c₂ = (1,0,0) ≠ 0`; O4 = examples 13-14), D4, D5 and D7 (10 rows, flag 15, first line says ">8 rows: REQ"; TL0 first): as in round 1.

## 6. Compiled nonempty instances (every endpoint statement)
```
$ grep -c "^example\|^theorem twFrame_inst" RBM3D/Probe/T2413Pins.lean
21
```
- `twFrame_inst` (289) discharges every deterministic premise of the frame:
  - datum: `sz0` (`L = 4`, `W = 32`), `zSeq`, `flow_sz0`, `(κ,ε,𝔡,𝔠) = (1/2,1/10,1/10,1/6)`;
  - window: `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`);
  - `STConStInd`: from `s1Setup_conStInd_const`;
  - regime: `STAny`.
- Examples 1-6 apply it to T.12′ and T.11 (i)-(v).
- Examples 7-11 instantiate TL1, the base case, `BAMainIndTL`, `BAMLOutTL` and `BAChainTL` at the same datum.
- Examples 12-20 cover D3/O3/O4, T.10 (a)-(d) at `Pf` (`v = 0 < u = 1/2` in (a), (b); `v < u` in (d)), and T.12″ with `σ = (−,+)`, `c₂ ≠ c₁`.
- Hypotheses left in the examples are other gates' pins only: `twSteps`, TL2 at `s`, `LWAvgLawgL`, `STLmaxgL`, `STG0M`, `STBaseG`, `STHorizonG`, and the probe's own pins. No `N = 0`, no empty index, no collapsed window, no `False` premise.

## 7. Paper deltas
- `T2413a`: none proposed (prove report (d) line 259, design line 109).
- The Theorem 8.2 change for TL1/TL2 is T2398d (`docs/DECISIONS.md:1975`).
- The remaining differences are Lean conventions, not paper statements: F1 (`g₀` against `g`, constant `A`), the pinned exponent 3/2, and the `ℓ¹`/`ℓ^∞` distances.
- The repair adds no Lean/paper difference: `STG0M` is the paper's `G_0 = M` (`1_2:1240`). Coverage is adequate.

## 8. Observations (no RETURN)
1. Design line 3 still says "probe ... (383 lines ...)" and lists commits up to `fcdfdc0`. Line 112 records `76c586e` and the line shifts. This is stale metadata and changes no statement.
2. The owner text for TL-V ("TL stage (TL2d one step; TL-V chain) + BA-V (V2a ...)") mixes the two texts of 0853:72, as noted in round 1. The dispatcher should accept or reword it when filing the >8-row REQ.
3. The round-1 observations on the row renaming (TL2c/TL2d/TL2e) and on `TP:165` at `(p,q) = (1,2)` stand.

## Verdict
PASS for every target:
- `BAChainTL` and the T.10 (d) instance (both repaired);
- the TL1 producer, the T.12′ step and frame, the base case, `BAMainIndTL`, `BAMLOutTL`;
- T.10 (a)-(d), T.12″, T.11 (i)-(v);
- the verbatim T2398 pins, D3-D7;
- build, axioms, diff scope.

Report-only merge: the probe stays on `t/T2413`.
