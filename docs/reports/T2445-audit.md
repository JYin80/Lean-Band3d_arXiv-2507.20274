Auditor model: claude-opus-5-5

# T2445 audit (round 1) — Mon Oct 12 11:06:02 UTC 2026

Branch `t/T2445` at `817dcbd`; audit worktree `../RBM3D-wt/T2445-audit1` (detached at `817dcbd`); merge base `23a4e69`.

## 1. Diff, size, hygiene
```
$ git diff --stat main...t/T2445
 RBM3D.lean                |    2 +
 RBM3D/BA/TwistFold2.lean  |  656 ++++
 RBM3D/BA/TwistFold2B.lean | 1066 ++++
 3 files changed, 1724 insertions(+)
$ git diff main...t/T2445 -- RBM3D.lean     (two lines after the last import, before #assert_rbm_axioms)
+import RBM3D.BA.TwistFold2
+import RBM3D.BA.TwistFold2B
$ grep -nwE 'sorry|admit|axiom|native_decide' RBM3D/BA/TwistFold2*.lean      -> (no output)
$ grep -nwE 'mE|STGM|STKloop|BATwist[A-Za-z0-9_]*|STLKgL' RBM3D/BA/TwistFold2*.lean
RBM3D/BA/TwistFold2B.lean:37:(no `k = 2`, `STLKgL`, `BATwist*`).        (docstring only)
$ for n in twLoop2X ... twFold2PrecDet; git grep -nwE "(def|theorem|lemma|abbrev) (n|n_holds)" main -- RBM3D | wc -l
all 11 names: 0
```
Only the sole writable files; no existing file touched, so no frozen signature changes. Both files are under the 2,000-line stop line (656, 1066).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.TwistFold2 RBM3D.BA.TwistFold2B
✔ [4006/4007] Built RBM3D.BA.TwistFold2 (5.4s)
✔ [4007/4007] Built RBM3D.BA.TwistFold2B (9.0s)
Build completed successfully (4007 jobs).            exit=0 (no error line; no warning line names either file)
$ lake build RBM3D 2>&1 | grep -E 'error|Build completed|assert'     (whole library, #assert_rbm_axioms last)
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
Build completed successfully (4272 jobs).            exit=0
```
`#print axioms` (scratch file, §3):
```
'RBM.BA.twLoop2X_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2_bound_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twVec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twMrow_le_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twMblk_le_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twB0_ge_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twEta_ge_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2Prec_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.twFold2PrecDet_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the check-file pins (term-mode, no tactic, plus `rfl` equality of the statement defs)
The auditor's scratch copy: `docs/tickets/checks/T2445-check.lean` with `import RBM3D.BA.TwistFold2`, `import RBM3D.BA.TwistFold2B` added, followed by:
```
example : T2445_twLoop2X_eq (fun d sz => @twLoop2X d sz) := fun _ _ _ _ _ _ _ _ => rfl
example : T2445_twLoop2X_trace (fun d sz => @twLoop2X d sz) := fun _ sz => @twLoop2X_trace _ sz
example : T2445_twFold2 (fun d sz => @twLoop2X d sz) := twFold2_holds
example : T2445_twFold2_bound (fun d sz => @twLoop2X d sz) := twFold2_bound_holds
example : T2445_twVec := twVec_holds
example : T2445_twMrow_le := twMrow_le_holds
example : T2445_twMblk_le := twMblk_le_holds
example : T2445_twB0_ge := twB0_ge_holds
example : T2445_twEta_ge := twEta_ge_holds
example (d : ℕ) : T2445_twFold2Prec (fun d sz => @twLoop2X d sz) d := twFold2Prec_holds d
example (d : ℕ) : T2445_twFold2PrecDet (fun d sz => @twLoop2X d sz) d := twFold2PrecDet_holds d
example : T2445_twFold2 (fun d sz => @twLoop2X d sz) = twFold2 := rfl
example : T2445_twFold2_bound (fun d sz => @twLoop2X d sz) = twFold2_bound := rfl
example : T2445_twVec = twVec := rfl        (also twMrow_le, twMblk_le, twB0_ge, twEta_ge: rfl)
example (d : ℕ) : T2445_twFold2Prec (fun d sz => @twLoop2X d sz) d = twFold2Prec d := rfl
example (d : ℕ) : T2445_twFold2PrecDet (fun d sz => @twLoop2X d sz) d = twFold2PrecDet d := rfl
$ lake env lean T2445Audit.lean     (scratch copy; the original #check output prints first, then the axioms above)
exit=0      (no error line)
```
So every target equals its pin up to the name (definitional equality, checked by `rfl`), and `twLoop2X` has the pinned body (`T2445_twLoop2X_eq` by `rfl`). Hypotheses, quantifier order (fixed parameters before `∀ᶠ n`), the loss `W^{-5d}` (target 3), the `G^*G` form (target 4), the frame of 7/7′ (`3 ≤ d`, `BAFlow`, `0 ≤ t ≤ BAflowT0`, `seqP (sz.withLam 0)`), the index type `(σ,a,b)` including `a = b`, and the right-hand side `(1−t)^{-1}Bctl^{5/2}` are all the pinned ones.

## 4. Hidden hypotheses, vacuity, cycles
- No `structure`, `class`, `inductive` or `axiom` in either file (declaration grep). Targets 2–7′ are `def … : Prop` with `_holds` theorems. Every new Prop-valued def that is public has a theorem concluding it. The helpers `TwistFold2_*` either carry the stem (§3 (E)) or are `private`.
- Stochastic premises: only `STLocalEntrygL` and `STLmaxgL`, both registered owed (`Test/Axioms.lean:133, 144`). `Test/Axioms.lean` is unchanged, and the full build's `#assert_rbm_axioms` passes (§2). `STLKgL`, `STDecaygL`, `LWAvgLawgL` and `BATwist*` are not used (grep §1).
- Dependencies are merged results only: the imports are `BA.TwistPins`, `Induction.ConArgDet` and `Graph.BAExp14aB`, all on `main`. There is no cycle: `TwistFold2B` imports `TwistFold2`, and nothing imports either.
- External hypotheses: none beyond the two owed pins, which the ticket authorizes as hypotheses only.

## 5. Compiled nonempty instances (in the files, built in §2)
| Target | Instance (file:line) | Data / discharge |
|---|---|---|
| 1 `twLoop2X`, `twLoop2X_trace` | `TwistFold2.lean:592, 595` | `sz0` (d=3, L=4, W=32), n=0, A=X=C=1, ρ=1[c=(a,a,a,a)]; value `= 1 ≠ 0` (`TwistFold2_inst_val`) |
| 2 `twFold2` | `:598` | same data |
| 3 `twFold2_bound` | `:601` | β=32768=W^d, r₁=r₂=1, all three bounds discharged |
| 4 `twVec` | `:612, 622` | `G = green [[0,1],[1,0]] i ≠ 0` (proved), M=½·1, φ=e₀, η=1; Ward hypothesis from `TwistFold2_gram_green` |
| 5a/5b | `:631, 635` | `BAMfine` at `sz0`, `zSeq`, n=0; `BASelf` from `BAflow_real … flow_sz0`; φ=1_[0] (nonzero) |
| 6a | `:642` | `sz0`, 𝔡=1/10 (`flow_sz0.1.2.2.2.2`), t≡1/2 → `∃ n` |
| 6b | `:647` | κ=1/2, `flow_sz0`, n=0, t=1/2 |
| 7′ | `TwistFold2B.lean:1047` | `sz0`, `zSeq`, t≡1/2 (`half_lt_t0`), root-#2 weight `ρ₀ = t²1[c₃=c₁∧c₄=c₂](M^B_{c₁c₂})²`, Cρ=1/4 by the M-Ward identity (`TwistFold2_rho2_bounds`); `STLocalEntrygL`, `STLmaxgL` kept as hypotheses |
| 7 | `TwistFold2B.lean:1034` | same data, X≡1; `‖X‖ ≺ W^d Bctl` discharged by `TwistFold2_one_prec` |

None of these is `N = 0`, an empty index, a collapsed window, a `False` premise or an astronomically large witness. Every deterministic hypothesis is discharged; only the two owed stochastic pins stay as hypotheses, as the ticket allows.

## 6. Paper deltas
Prove report (d)5 proposes **T2445a**, **T2445b** and **T2445c**:
- T2445a: the fold with root `W^{-5d}` and `G^*G`, in place of the second `GG` step of B:118.
- T2445b: the averaged, pathwise row with the `X`-factor, and `∀ᶠ n`.
- T2445c: S3A-C1 through the BA tie of `M`, with no band formula.

These cover every Lean/paper difference of the targets. The unused pinned hypotheses `3 ≤ d`, `0 < ε`, `0 < 𝔡` (report (d)4) weaken nothing.

## 7. Observations (no RETURN)
1. Ticket item 8 states the value of the target-1 instance as `W^{-2d}`. The pinned body evaluates to `W^{-3d}·W^{3d} = 1`, and that is what the file proves. The value is nonzero either way. This is a ticket-arithmetic slip, not a defect of the branch.
2. DECISIONS §257 names "the S3A-C1 expansion (three cross terms, 2-loop bounds)" as required content of the proof. The proof takes a different route:
   - it splits `φ = φ^G − φ^M`;
   - it uses `STLmaxgL` at `k = 1, 3` only;
   - it uses no `k = 2` and no band formula (`BAMfine_eq` is used; the grep in §1 is clean).

   The pinned statement is unchanged and holds. The prover flagged this in (d)1 and in T2445c. If L4d2b wants the `𝓛^{(2)}` form, it is not provided here.
3. Process claim not re-verified: the report says no warning names either file. The audit build output in §2 agrees.

## Verdicts
| Target | Verdict |
|---|---|
| 1 `twLoop2X`, `twLoop2X_trace` | PASS |
| 2 `twFold2` | PASS |
| 3 `twFold2_bound` | PASS |
| 4 `twVec` | PASS |
| 5a `twMrow_le`, 5b `twMblk_le` | PASS |
| 6a `twB0_ge`, 6b `twEta_ge` | PASS |
| 7 `twFold2Prec` | PASS |
| 7′ `twFold2PrecDet` | PASS |
| 8 instances | PASS |

**Overall: PASS.** No dispatcher sign-off is needed.
