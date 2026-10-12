Auditor model: claude-opus-5-5

# T2468 audit (round 1): BA-G G7, the primed Step-1 rewire

Written Mon Oct 12 19:33:51 UTC 2026 (`date -u`); branch `t/T2468` at `cd0ab2da` (merge base `03109267`; `main` now `ad52b370`).
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2468-audit1` (detached at `cd0ab2da`). Scratch: `<scratchpad>/T2468/`.

## 1. Diff scope (G1, target 10)
```
$ git diff main...t/T2468 --stat
 RBM3D.lean               |    1 +
 RBM3D/BA/Step1Prime.lean | 1181 ++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   12 +-
$ git diff main...t/T2468 -- RBM3D/Test/Axioms.lean | grep -cE "^[-+] "   # 6 removed, 6 added
12
```
Registry edits, read one by one: (a) `BAGbEXPij` removed from `owedProps`; (b) added last in `supersededProps` (the `STLWT` line's `]` became `,`); (c) `STKboundgL` instances text; (d) `STGiiGEXgL`/`STGavLGEXgL` BA owner "proved at `baFMz` (… T2468)"; (e) `STGijGEXgL` BA owner "not produced in the window shape … T1-BA, DECISIONS §272". They match the ticket's Registry (a)-(e). Only the sole writable files; no merged Step-1/Green/KBound file is touched, so their statements are unchanged. `Step1PrimeB.lean` not created (1181 lines < stop line 2,000).

## 2. Build and axioms
```
$ lake build RBM3D.BA.Step1Prime        (audit worktree)
Build completed successfully (3829 jobs).
$ lake build                            (full library, runs #assert_rbm_axioms with the registry edits)
non-vacuity certificates: 0 of 106 premises in the two ledgers; ...
Build completed successfully (4298 jobs).
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/BA/Step1Prime.lean
(no output)
$ lake env lean audit_check.lean | grep "depends on axioms" | sed 's/.*axioms: //' | sort | uniq -c
  22 [propext, Classical.choice, Quot.sound]
```
The 22 `#print axioms`: `baGij'_member`, `step1Prime_loopPrem`, `step1Prime_wl_det`, `baS1_{wl_seq,forb,boot,weakPT,loopPT}'`, `baBootstrap'_of_ij'`, `baStep1_of_ij'`, `baBootstrap'_holds'`, `baStep1_holds'`, `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds`, and the instances `inst_baBootstrap'_ij'`, `inst_baStep1'`, `inst_baStep1'_low`, `inst_baGij'_member`, `inst_step1Prime_wl_det`, `inst_step1Prime_loopPrem`, `inst_baS1_wl_seq'`, `inst_baS1_loopPT'`.

## 3. Statements against the pins (targets 1, 4-7)
`audit_check.lean` = the check file `docs/tickets/checks/T2468-check.lean` verbatim (Parts 1-3) + `import RBM3D.BA.Step1Prime` + the lines below, compiled on the branch:
```
example : T2468_GijMember' := baGij'_member
example : T2468_BootstrapIj' := baBootstrap'_of_ij'
example : T2468_Step1Ij' := baStep1_of_ij'
example : T2468_BootstrapHolds := baBootstrap'_holds'
example : T2468_Step1Holds := baStep1_holds'
example : T2468_STGiiBA := baSTGiiGEXgL_holds
example : T2468_STGavBA := baSTGavLGEXgL_holds
example : T2468_InstBootstrap := Step1PrimeInst.inst_baBootstrap'_ij'
example : T2468_InstStep1 := Step1PrimeInst.inst_baStep1'
$ lake env lean audit_check.lean; echo "exit $?"; grep -c error check_out.txt
exit 0
0
```
All nine pins are inhabited by the named theorems, so targets 1, 4, 5, 6 and 7 equal their pins up to the name. The check file compiles on the branch.
Quantifier order in target 1 (`Step1Prime.lean:99-112`): `∀ κ ε 𝔡`, then `∃ c > 0`, then `∀ 𝔠 sz z`. This is fixed by the pin. In the proof (`:114-115`), `(κ', ε')` come from `BAFlowMember` before `c` (the stem copy `Step1Prime_member`, `:54-61`, has `∃ κ' ε'` before `∀ 𝔠 sz`).

## 4. Statement diff, target 3 (merged `Step1.lean` vs `Step1Prime.lean`, by script)
```
$ python3 -I stmt.py RBM3D/BA/Step1.lean RBM3D/BA/Step1Prime.lean baS1_wl_seq baS1_forb baS1_boot baS1_weakPT baS1_loopPT
== baS1_wl_seq: merged 15 lines, primed 26 lines; removed 2 added 13
== baS1_forb: merged 14 lines, primed 25 lines; removed 2 added 13
== baS1_boot: merged 14 lines, primed 25 lines; removed 2 added 13
== baS1_weakPT: merged 16 lines, primed 27 lines; removed 2 added 13
== baS1_loopPT: merged 17 lines, primed 28 lines; removed 2 added 13
five diffs identical apart from the theorem line: True
-theorem baS1_forb (d : ℕ) :
+theorem baS1_forb (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
-    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGijGEX sz z' u ε₀) →
+    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
+      ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
+        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
+        (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
+        (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
+        GreenCore_loopPrem sz z' u ε₀ Φ →
+        PrecL sz (Sizes.seqP (sz.withLam 0))
+          (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
+          (fun n p ω => (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
+            ‖(baFMz sz z').GM n (u n) ω p.1.1 p.1.2‖)
+          (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1)
+            (Sizes.STblk sz n p.1.2))) →
```
- The new family is the body of `GreenCore_decayConcl sz z' u ε₀ D c Φ Ψ` (`GreenCore.lean:1627-1633`), unfolded: the text matches. Lean confirms it: `baBootstrap'_of_ij'` (`Step1Prime.lean:864-876`) builds `hGij` with the folded `GreenCore_decayConcl` type and passes it to `baS1_loopPT'`/`baS1_weakPT'`, and this compiles.
- Every other hypothesis and every conclusion is verbatim. The only additions are the binders `c`, `hc` (the "with its `c`" of the ticket) and the guard `hd : 2 ≤ d` (see Observation O1).
- Target 2 (a), `step1Prime_loopPrem` (`:321-330`): it concludes `GreenCore_loopPrem sz z' u ε₀ (fun n _ _ => Bctl_n(s_n)^{7/15})` for every `ε₀ > 0` from `S1Std`, `0 < κm ≤ Im m`, and the `k = 2` loop input. This is the ticket's shape, with `ε₀ = c'` as a special case.
- Target 2 (b), `step1Prime_wl_det` (`:221-234`): the off-diagonal hypothesis is `indMax · ‖GM_xy‖ ≤ Nτ · GreenCore_decayRHS … c (d/2) (fun _ _ => φ) φ`. The conclusion constant `Step1Prime_K d c = 3·expC(d-2, c/d)^4 + 4` (`:143`) depends on `(d, c)` only and is not a binder of any target statement (2254 Q3).

## 5. Vacuity, hidden hypotheses, cycles
- No new `structure`/`class` and no new `Prop` pin (`grep -nE "^(structure|class)"`: none).
- The public results carry only these premises: merged `Prop`s (`BAFlowMember`, `BAGbEXPii`, `BAGbEXPij'` in target 4, discharged in target 5), the unchanged premises inside `BABootstrap'`/`BAStep1`, and, in target 3, the conditional families as in the merged originals.
- Upstream signatures (merged, by grep): `baGbEXPij'_holds (d) (hd : 2 ≤ d) : BAGbEXPij' d` (`GreenOff:1289`), `baGbEXPii_holds (d) (hd : 2 ≤ d)` (`GreenLocal:474`), `baGbEXPav_holds (d) (hd : 2 ≤ d)` (`GbEXPav:24`), `BAFlowMember_holds (d) : BAFlowMember d` (`Step1Fam:624`), `inst_BAKbound : STKboundgL (baFMz sz0 zSeq) (seqP (sz0.withLam 0))` (`KBound:334`).
- No cycle: the axiom prints show the standard three only. No external hypothesis is introduced, so no limit check is required.
- Premise scan on the built library (`scanPremises` from `RBM.Audit`, scratch `scan.lean`):
```
RBM.BA.BAGbEXPij: found=true superseded=true owed=false
RBM.BA.BAGbEXPij': found=false superseded=false owed=false
RBM.BA.GreenCore_decayConcl: found=false superseded=false owed=false
RBM.BA.GreenCore_loopPrem: found=false superseded=false owed=false
RBM.BA.BAGbEXPii: found=false superseded=false owed=false
RBM.BA.STGiiGEXgL: found=false superseded=false owed=true
RBM.BA.STGavLGEXgL: found=false superseded=false owed=true
RBM.BA.STGijGEXgL: found=true superseded=false owed=true
RBM.BA.STKboundgL: found=false superseded=false owed=true
```
`BAGbEXPij` is found and classified as superseded. No new unregistered premise. `STGii/STGav/STKbound` are registered but no longer found; the ticket says this is a report line, not a failure.

## 6. Compiled nonempty instances (namespace `RBM.BA.Step1PrimeInst`, same file)
Common data: `d = 3`, `sz0` (`L=4`, `W=32`, `N=2097152` at `n=0`), `zSeq` with `flow_sz0`, `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `𝔠d=1/100`, `c₁=1/3`, `(s,t)=(1/2,2/3)` and `(0,1/16)`.

| Target | Instance (line) | Hypotheses left |
|---|---|---|
| 1 `baGij'_member` | `inst_baGij'_member` (946): `baGbEXPij'_holds 3`, `BAFlowMember_holds 3`, `sz0_win_third`, `BAFamZ_main` | none (Φ, Ψ remain universally quantified, which is the pin's shape) |
| 2a `step1Prime_loopPrem` | `inst_step1Prime_loopPrem` (964): `inst_baS1Std`, `inst_im_m_ge`, `inst_hLI` | none |
| 2b `step1Prime_wl_det` | `inst_step1Prime_wl_det` (973): `n=0`, `u=0`, `c=1`, `φ=1/10`, `Nτ=4`, `C₀=3` | none (see O2) |
| 3 `baS1_*'` | `inst_baS1_{wl_seq,forb,boot,weakPT,loopPT}'` (1049-1104) | `hLoc` only (BA-V) |
| 4a/7a | `inst_baBootstrap'_ij'` (1110): `hK := inst_BAKbound`, `hmem`, `hwin`, `hii`, `hij'`, `STConStInd`, ConArg discharged | `hLK`, `hLoc` (= pin) |
| 4b/5b/7b | `inst_baStep1'` (1127), `inst_baStep1'_low` (1144) | the family premise (= pin) |
| 4b, 5, 6 | `example : BAStep1 3 := baStep1_of_ij' …` (1161); `example : BABootstrap' 3 ∧ BAStep1 3` (1164); `example : STGiiGEXgL`/`STGavLGEXgL (baFMz sz0 zSeq) … tI (1/10)` (1168, 1172); optional `inst_BALmaxFromLK inst_BAKbound` (1177, `hLK` left) | none |

All compile (module build above). None has `N = 0`, an empty index, a collapsed window (`s < t` strictly), or a `False` premise. The hypotheses left are BA-V's merged premises, which the ticket allows ("Inputs used as hypotheses only" (c)).

## 7. Rules (target 9), audit greps
```
$ grep -nE "BAGbEXPij([^'_A-Za-z0-9]|$)|BAGijGEX|gexRHS|baGij_member|baBootstrap'_holds([^'_]|$)|baStep1_holds([^'_]|$)" Step1Prime.lean  (classified against /- … -/ ranges)
15 doc 16 doc 95 doc 218 doc 371 doc 845 doc 846 doc 878 doc
$ grep -nE "m₀|Cλ|g ≤ W" Step1Prime.lean                                 -> (no output)
$ grep -nE "TwistStep2_lam0_sq|gK|lam0 n ≤|sz\.lam n \^ 2" Step1Prime.lean -> (no output)
$ grep -n "^import" Step1Prime.lean
6:import RBM3D.BA.GbEXPav
7:import RBM3D.BA.KBound
```
(a) The unprimed names occur only in docstrings. (b) and (c): no hits. (d) No `Chain/Step34Gen`, U, V or T-BA import.

## 8. Paper deltas
The `2 ≤ d` guard on targets 4-6 (paper: `d ≥ 3`) is already covered by D671 (T2403a) and D675 (b) (T2408b) in `docs/paper-deltas.md:1635, 1639`. The prove report (d) proposes `T2468a` (informational): `baS1_*'` carry `hd : 2 ≤ d`, the explicit rate `c` and `0 < c`, and Step 1's window constant `3S⁴+4` is internal to Lean. No other Lean/paper statement difference was found. Coverage is complete.

## 9. Observations (not RETURN)
- O1. Target 3 says "one change", but `baS1_*'` also add `hd : 2 ≤ d`, which `BAsum_exp_decay_le` in the core needs. The prove report records this ((a′), (d), T2468a). It changes no endpoint: the pinned targets 4-5 carry the same guard, and the rate `c` comes from `BAGbEXPij'`, which is only proved for `2 ≤ d`.
- O2. `inst_step1Prime_wl_det` uses `n = 0`, `u = 0`, where `G − M = 0`, so its conclusion holds trivially. This mirrors the merged `inst_flowFM_wl_det`. The data are nondegenerate, and the core is used non-trivially in `inst_baS1_wl_seq'`, where every hypothesis is discharged.
- O3. The prove report (b) leaves out `inst_baS1_*'` when it lists the axiom prints of the instances. This audit printed `inst_baS1_wl_seq'`/`_loopPT'` (standard three).
- O4. Merge note for the hub: `main` has moved (`ad52b370`). `RBM3D.lean` and `Test/Axioms.lean` need the union with T2457/T2462 registry lines (H23 (b)), then the full build.

## Verdict
| Target | Verdict |
|---|---|
| 1 `baGij'_member` | PASS |
| 2 (a) `step1Prime_loopPrem`, (b) `step1Prime_wl_det` | PASS |
| 3 `baS1_wl_seq'`, `baS1_forb'`, `baS1_boot'`, `baS1_weakPT'`, `baS1_loopPT'` | PASS (O1) |
| 4 `baBootstrap'_of_ij'`, `baStep1_of_ij'` | PASS |
| 5 `baBootstrap'_holds'`, `baStep1_holds'` | PASS |
| 6 `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds` | PASS |
| 7 instances | PASS |
| 8 registry (a)-(e) | PASS (full build with `#assert_rbm_axioms` passes; scan above) |
| 9, 10 rules / G1 | PASS |

**Ticket T2468: PASS.** No dispatcher sign-off needed.
