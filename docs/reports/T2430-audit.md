Auditor model: claude-opus-5-5

# T2430 audit (round 1): BA-TL TL2c, `baTwistSrc3_holds` (T.11 (iii))

Written Mon Oct 12 00:26:07 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2430-audit1`, detached at `t/T2430` = `66632ff`.
Scratch files: scratchpad `T2430/` (`AuditT2430.lean`, `check.lean`, `InstCopy.lean`, `build.log`, `inst.log`).

## 1. Statement (target 1) against the ticket's pin

```
$ diff <(grep -o '`baTwistSrc3_holds (d : ℕ) (R : [^`]*`' docs/tickets/T2430.md | head -1 | tr -d '`') \
       <(grep -o '^theorem baTwistSrc3_holds.* :=' RBM3D/BA/TwistQV.lean | sed 's/^theorem //; s/ :=$//'); echo diff-exit=$?
diff-exit=0
$ grep -nE "^(theorem|lemma|def|abbrev|noncomputable def)\b" RBM3D/BA/TwistQV.lean     # public declarations
1385:theorem baTwistSrc3_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc3 d R := by
$ git diff $(git merge-base main HEAD) main -- RBM3D/BA/TwistPins.lean RBM3D/BA/EMn2BA.lean RBM3D/Induction/Contract.lean RBM3D/BA/FlowPins.lean | wc -l
       0
```
The conclusion is the merged pin `BATwistSrc3 d R` itself (`BA/TwistPins.lean:265`, frame `BATwFrame` `:146`; both unchanged on the branch and on `main` since the merge base `0a8176c`). It holds for every `d` and every regime `R`, with no extra hypotheses. Against the ticket's mathematics, it gives:
- conjunct 1: `∀ p q ≥ 1`, `twSrc … ‖twEE … b b …‖ (Ξ = 1) (4 - 1/(2p) - 1/q)`, uniform over `TimeIcc s t × σ × b × c₁ × c₂`, i.e. `Q_v(b) ≺ η_v⁻¹ (W^{-d}B_{v,0})^{4-1/(2p)-1/q}`;
- conjunct 2: the deterministic CS bound `|(Ẽ⊗Ẽ)(b,b')| ≤ √(Q(b)Q(b'))` for all `n v ω σ b b' c₁ c₂`.

Quantifier order: `3 ≤ d → ∀ κ ε 𝔡 → ∀ Cd → ∃ 𝔠d ∈ (0, 1/100] → ∀ 𝔠 sz z …`, as pinned. The witness is `𝔠d = 1/100` (line 1387), a fixed constant that does not depend on `sz`. This is the ticket's "take `𝔠d` as the proof gives it".

The check file fits the target (pinned form `T2430_Target`, for every `R`):
```
$ cat AuditT2430.lean   # check-file imports + `import RBM3D.BA.TwistQV` + check-file defs/examples (no #check) + :
example : T2430_Target 3 := fun R => RBM.BA.baTwistSrc3_holds 3 R
example : ∀ d, T2430_Target d := fun d R => RBM.BA.baTwistSrc3_holds d R
#print axioms RBM.BA.baTwistSrc3_holds
$ lake env lean AuditT2430.lean; echo exit=$?
'RBM.BA.baTwistSrc3_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean docs/tickets/checks/T2430-check.lean (copy) >/dev/null; echo check-file exit=$?
check-file exit=0
```
Target 1 statement: **PASS** (verbatim pin, general `R`, general `d`; not a special case).

## 2. Hidden hypotheses, vacuity, cycles

```
$ sed -n 1385,1390p RBM3D/BA/TwistQV.lean
theorem baTwistSrc3_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc3 d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htT hR hcon hsteps
  exact ⟨fun p q hp hq => TwistQV_src hκ sz hflow s t hs htT (by norm_num) hcon hsteps.2.1 p q hp hq,
    fun n v ω σ b b' c₁ c₂ => TwistQV_cs (baFMz sz z) n rfl v ω σ b b' c₁ c₂⟩
$ grep -nE "^\s*(structure|class|axiom|instance)\b" RBM3D/BA/TwistQV.lean | wc -l
0
$ sed -n 1247,1253p RBM3D/BA/TwistQV.lean     # the conjunct-1 engine: its only stochastic input is twSteps' conjunct 2
private theorem TwistQV_src {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (s t : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n)
    {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t)
    (hL : ∀ k : ℕ, 1 ≤ k → PrecL sz (Sizes.seqP (sz.withLam 0))
      (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖(baFMz sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1)))
```
- The proof takes no new structure and no new hypothesis. It uses only frame premises: `BAFlow`, `s ≥ 0`, `t ≤ BAflowT0`, `STConStInd` and `twSteps.2.1`, which is (I3) = (2.89) and the ticket's input (a). `R`, `Cd` and `hst` are unused, as the ticket says. `twSteps.1`, `.2.2.1` and `.2.2.2` (Claim 4.5 and the rest) are unused.
- Conjunct 2 is a theorem about any carrier with `S n = 1`, discharged by `rfl` at `baFMz` (input (ii)).
- No cycle: the imports are `BA.TwistPins`, `BA.EMn2BA` and `Induction.Contract`, all merged on `main`. `git diff main...t/T2430` adds only `RBM3D/BA/TwistQV.lean`.
- The external hypothesis is `twSteps` (Steps 1–4, owed by other gates), and it appears only in the instance. The prove report's §(a)(2) gives its concrete limit check: `B_n(2/3)·(2(n+1))^{15} → 3`, so the right-hand sides are positive and finite, and `k = 1` gives `|Tr(GE_b)| ≺ 1`.

Result: **PASS**.

## 3. Compiled nonempty instance

`RBM3D/BA/TwistQV.lean:1412-1425`, an `example`:
- It applies `baTwistSrc3_holds 3 STAny` through `TwistQV_frame_inst` at `sz0` with `(κ,ε,𝔡,𝔠) = (1/2,1/10,1/10,1/6)`, `flow_sz0`, `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0` (`t0_sz0`) and `STConStInd` (`s1Setup_conStInd_const`).
- It reads off conjunct 1 at `(p,q) = (2,2)` (exponent `13/4`, the consumer point).
- It reads off conjunct 2 at `n = 0`, `v = 1/2`, `σ = ![false,true]`, `b = 0 ≠ b' = ![1,0,0]` and `c₁ = 0 ≠ c₂ = ![1,0,0]` in `Zd 3 (sz0.L 0)`, with `L 0 = 4`. Both inequalities are proved in Lean.
- The only hypotheses left are `0 < Cd` and `twSteps` (the other gates' pin), which the ticket allows. Every deterministic hypothesis is discharged.
- Nothing is degenerate: `N = (W L)^3 > 0`, the window is nonempty, there is no `False` premise and no astronomical witness in the statement itself.

To print axioms, I compiled the instance as a named theorem in a scratch copy of the whole file. This re-elaborates all 1429 lines independently of the lake build:
```
$ sed 's/^example {Cd : ℝ} (hC : 0 < Cd) (hS : twSteps/theorem TwistQV_inst_audit {Cd : ℝ} (hC : 0 < Cd) (hS : twSteps/' \
    RBM3D/BA/TwistQV.lean > InstCopy.lean; echo '#print axioms RBM.BA.TwistQV_inst_audit' >> InstCopy.lean
$ lake env lean InstCopy.lean > inst.log 2>&1; echo exit=$?; grep -c error inst.log; grep warning inst.log | head
exit=0
0
$ grep axioms inst.log
'RBM.BA.TwistQV_inst_audit' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Result: **PASS**.

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.BA.TwistQV > build.log 2>&1; echo exit=$?
exit=0
$ grep -n TwistQV build.log; grep -c "^error" build.log; tail -1 build.log
3309:✔ [4010/4010] Built RBM3D.BA.TwistQV (6.8s)
0
Build completed successfully (4010 jobs).
```
(The other warnings in `build.log` are from upstream merged modules. None are in `TwistQV.lean`.)
```
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/BA/TwistQV.lean; echo grep-exit=$?
grep-exit=1
$ git diff --name-only main...t/T2430
RBM3D/BA/TwistQV.lean
$ git diff main...t/T2430 -- RBM3D/BA/TwistPins.lean RBM3D.lean | wc -l
       0
$ grep -rn "baTwistSrc3_holds\|TwistQV_" <all .lean files on main> | wc -l     # name clash
       0
$ wc -l RBM3D/BA/TwistQV.lean
    1429 RBM3D/BA/TwistQV.lean      # stop line 2000, split threshold 1700: no split needed
```
- Axioms: `baTwistSrc3_holds` and the instance depend only on `[propext, Classical.choice, Quot.sound]` (§1, §3).
- The diff touches only the sole writable file. `RBM3D.lean` is untouched; the hub adds the import at merge. No probe file and no `TwistQV2.lean`.
- No frozen signature is changed. Every helper is `private` with the stem `TwistQV_`; the only public name is the pinned one.

Result: **PASS**.

## 5. Paper deltas

| Lean/paper difference | coverage |
|---|---|
| The C₂ term `(W^{-d}B)^{4-1/(2p)}` is absorbed into exponent `4-1/(2p)-1/q` using `B ≤ 1` on `[s,t]`, which TP:144 does not state; Lean takes `B_t < 1` from `STConStInd` and uses `STBctl_mono` | candidate **T2430a** (prove report §(d)) |
| The statement form (frame, `twSrc`, `twEE`, `S = 1` weight, `𝔠d ≤ 1/100`) | it is the merged pin of TL0 (T2421); this ticket adds no statement difference |
| (B.3) is proved inline (`TwistQV_R2`, private), not as a standalone lemma | proof route only, no statement difference |

Result: **PASS**.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
1. The ticket's sentence "the proof uses neither `Cd`, nor `STConStInd`, nor `R`" does not match the proof, which uses `STConStInd` (only for `B_t < 1`). This is the ticket's own input (c), "`Bctl ≤ 1` on `[s,t]`", which needs a source. The prove report states the mismatch.
2. The reuse differs from the ticket's suggested list: `ContractPt.lean:73-116` and the TwistPins twisted-sum helpers (`:292-345`) are not used. 25 private tools from `Induction/Contract.lean` and 1 from `Path/LemDecCalEdif.lean:444` are copied under the `TwistQV_` stem, with sources cited.
3. Section (a) omits the ticket's preflight items (iii) (the reuse table) and (v) (the line prediction), citing CLAUDE.md §4 step 1. Section (b) gives the reuse table, and the final line count is 1429.
4. The instance's `STConStInd` holds only eventually (from `n = 8` at `𝔠d = 1/100`, per the prove report). That is the pinned `∀ᶠ` form, discharged in Lean by the merged `s1Setup_conStInd_const`, so it is not a degenerate witness.

## Verdict

| target | verdict |
|---|---|
| `baTwistSrc3_holds` (both conjuncts, every `d`, every `R`) | **PASS** |
| instance (`TwistQV.lean:1412`) | **PASS** |

T2430: **PASS**. No dispatcher sign-off needed.
