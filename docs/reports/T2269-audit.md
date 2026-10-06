Auditor model: claude-opus-5-5

# T2269 audit, round 1 (BA-S2b2b, `RBM3D/BA/Step1.lean`), Tue Oct  6 08:36 UTC 2026

Branch `t/T2269` at 7932bb0 (merge-base c77e68c); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2269-audit1` (detached).

## 1. Diff scope and frozen signatures
```
$ git diff --stat main...t/T2269
 RBM3D/BA/Step1.lean    | 784 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   4 +-
$ git diff main...t/T2269 --stat -- RBM3D/BA/Step1Boot.lean RBM3D/BA/Step1Setup.lean RBM3D/BA/FlowPins.lean
(empty)
$ grep -n "^import" RBM3D/BA/Step1.lean
6:import RBM3D.BA.Step1Setup
7:import RBM3D.BA.Step1Boot
8:import RBM3D.Induction.Continuity
9:import RBM3D.Induction.PerTimeCalc
10:import RBM3D.Induction.Step1Setup
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/Step1.lean
(no output)
```
Both files are the ticket's sole writable files; imports are within the allowed list (no `RBM3D`, no `RBM3D.Induction.Step1`). The merged pin `BABootstrap'` is untouched. Unpinned helpers are all `private` (`BAStep1_*`, `lamS_two_thirds'`).

## 2. Statements against the check file (`docs/tickets/checks/T2269-check.lean`)
Scratch file = check file + `import RBM3D.BA.Step1` + the acceptance examples + `#print axioms`:
```
example : @RBM.BA.FlowFM.gmMax = @RBM.BA.T2269Check.gmMax := rfl
example (d : ℕ) : baBootstrap'_holds_stmt d := RBM.BA.baBootstrap'_holds d
example (d : ℕ) : baS1_wl_seq_stmt d := RBM.BA.baS1_wl_seq d      -- and baS1_forb, baS1_boot, baS1_weakPT, baS1_loopPT
$ lake env lean scratchT2269/stmt.lean; echo exit $?
exit 0
$ python3 sd.py   # whitespace-normalised text of `def *_stmt` body vs theorem type
baS1_wl_seq IDENTICAL 1031 1031
baS1_forb IDENTICAL 983 983
baS1_boot IDENTICAL 972 972
baS1_weakPT IDENTICAL 1061 1061
baS1_loopPT IDENTICAL 1102 1102
baBootstrap'_holds IDENTICAL 59 59
gmMax body IDENTICAL 121 121
```
All seven statements match the pin character for character (after whitespace normalisation) and by `rfl`/defeq. Hypotheses, quantifier order, the time range `u ∈ [s,t]`, `k ≥ 1`, the threshold `1 + κm⁻¹`, the bounds `2·3^d a_s^{7/15}`, `a_s^{1/4}`, `Bctl n u ^ (1/4)` and the loop bound `((1−s)/(1−u))^{k−1} a_s^{k−1}` are those of the ticket. Target 6 is the general merged pin `BABootstrap' d` for all `d`, not a special case.

## 3. Vacuity, hidden hypotheses, cycles
- No new `structure`/class; the only new definition is the `ℝ`-valued `FlowFM.gmMax` (finite `sup'` over a nonempty `Finset.univ`).
- `baBootstrap'_holds` (Step1.lean:576-597) intros the pin's premises, uses `baS1Std`, `BAFamZ_mono`, `BAFamZ_im_m_ge`, `baBoot_LI` (with `(hcon u h1 h2).1`), `baGii_member`, `baGij_member`, `baNetLift`, targets 4 and 5. Its inputs `BAFlowMember`, `BAGbEXPii`, `BAGbEXPij` are merged owed pins defined before `BABootstrap'` (`Step1Boot.lean:108-133` < `:148`), so no cycle. `hK`, `hLK`, `hsT`, `.2` of `hcon` are unused (the report's T2269b).
- All dependencies are merged on `main` (the ticket's list; the file imports only merged modules and builds).
- External hypothesis `BAWinBulk sz0 zSeq (1/3) (1/2)` (as T2238/T2256): limit check in the prove report (a)(ii)(C): `Im m(E_n, g0) = 0.99949, 1.00000` at `n = 0, 1` (≥ κ = 1/2), and T2262 (a)(ii)(F).

## 4. Compiled nonempty instances (namespace `RBM.BA.Step1Inst`, same file)
```
$ grep -n "^theorem inst_" RBM3D/BA/Step1.lean
633 inst_hcon_full  673 inst_hLI  686 inst_hGii  694 inst_hGij  703 inst_baS1_wl_seq  715 inst_baS1_forb
726 inst_baS1_boot  736 inst_baS1_weakPT  748 inst_baS1_loopPT  764 inst_baBootstrap'  780 inst_gmMax_zero
```
Data: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2^21`), `zSeq`, `z' = zSeq` (`BAFamZ_main`), `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`, `c₁ = 1/3`, `s ≡ 1/2 < t ≡ 2/3 ≤ t₀` (`t0_sz0`), `κm = 1/2`, `u ≡ 2/3` for target 1, every `k ≥ 1` for target 5. Nondegenerate: nonempty window, `N ≥ 2^21`, no `False` premise.
- Discharged deterministically: `flow_sz0`, `sz0_lam_pos`, all time and parameter inequalities (`norm_num`), `inst_baS1Std`, `inst_im_m_ge`, `inst_norm_m_le`, `STConStInd` (`s1Setup_conStInd_const`), both halves of the ConArg premise (`inst_hcon_full`, from `baConArg''_holds 3` and `BATrivialLmax_holds`), the loop input (`inst_hLI` = `baBoot_LI`).
- Kept as hypotheses (allowed by the ticket: other gates' pins / external window): `BAFlowMember 3`, `BAGbEXPii 3`, `BAGbEXPij 3`, `hwin`, and `STKboundgL`, `STLKgL`, `STLocalMaxgL` of `baFMz sz0 zSeq` at `sI`.
- `inst_gmMax_zero : (baFMz sz0 zSeq).gmMax 0 0 ω = 0` from `inst_GM_zero`.
Every endpoint theorem (targets 1-6) has an instance at this data. The ticket's `hvec` was derived, not kept.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.Step1
Build completed successfully (3756 jobs).
exit 0
$ lake build                          # full library (root has no BA.Step1 import until merge)
Build completed successfully (4076 jobs).
exit 0
$ lake env lean scratchT2269/stmt.lean | grep "depends on axioms" | sort | uniq -c
  15 depends on axioms: [propext, Classical.choice, Quot.sound]
```
(15 = the six targets, `FlowFM.gmMax`, the seven `inst_baS1_*`/`inst_baBootstrap'`/`inst_gmMax_zero`, `inst_hcon_full`.) No error lines in either build log.

Registry pre-check (DECISIONS §20 (2)):
```
$ printf "import RBM3D\nimport RBM3D.BA.Step1\n#assert_rbm_axioms\n" > scratchT2269/precheck.lean; lake env lean scratchT2269/precheck.lean
axiom audit: 7899 theorems, 2609 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.STKboundgL: 3 [no certificate]
  RBM.BA.STLKgL: 4 [no certificate]
  RBM.BA.STLocalMaxgL: 9 [no certificate]
exit 0
$ (lines of the pre-check output naming BABootstrap'): 0
$ owedProps entries (awk over `def owedProps`): main 154, t/T2269 156
$ git diff main...t/T2269 -- RBM3D/Test/Axioms.lean | grep "^[-+]   \`"
+   `RBM.BA.STKboundgL, ... hypothesis of the instance `inst_baBootstrap'` (T2269); owed ...
+   `RBM.BA.STLKgL, ... hypothesis of the instance `inst_baBootstrap'` (T2269); owed ...
+   `RBM.BA.STLocalMaxgL, ... hypothesis of the instances `inst_baS1_boot`, ... (T2269); owed ...
-   `RBM.BA.BABootstrap', -- BA Step 1 bootstrap for one member of `Fam(t)` ...
$ git grep -n "STKboundgL\|STLKgL\|STLocalMaxgL" main -- RBM3D | grep -v FlowPins.lean   # prior hypothesis uses
main:RBM3D/BA/Step1Boot.lean:156-158  (inside the Prop pin `BABootstrap'` only)
main:RBM3D/BA/UNPins.lean:108,113,1016 (docstring / inside the Prop pin `UNMLOut`-shape conjunction / its instance conclusion)
```
On `main` no theorem took these three predicates as hypotheses; the ticket-mandated instances are the first, so `#assert_rbm_axioms` needs them registered. The added lines are append-only registry lines (§20 (1)), classified owed (§20's default when uncertain, flagged by the prover as T2269c).

## 6. Paper deltas
- T2269a (Step 1 read with the continuity argument on `‖G_u − M‖_max`, threshold `1 + κ⁻¹`, uniform `PrecL` loop input) and T2269b (unused premises of `BABootstrap'`: `STKboundgL`, `STLKgL`, `BAConArgVec`, `s ≤ t₀(z)`, strictness of `s < t`) are proposed in prove report (d). They cover the Lean/paper differences seen in §2-§3. Neither is in `docs/paper-deltas.md` yet (`grep -n T2269` there: no output); proposing them is enough.

## 7. Verdicts
| target | verdict |
|---|---|
| 0 `FlowFM.gmMax` (vocabulary) | PASS |
| 1 `baS1_wl_seq` | PASS |
| 2 `baS1_forb` | PASS |
| 3 `baS1_boot` | PASS |
| 4 `baS1_weakPT` | PASS |
| 5 `baS1_loopPT` | PASS |
| 6 `baBootstrap'_holds` | PASS |

Overall: **PASS**.

## 8. Observations (no statement, instance, build, axiom or paper-delta effect)
- O1 (registry deviation from the ticket text). The ticket said "no line added" and owed count = main's − 1; the branch adds three owed lines (`STKboundgL`, `STLKgL`, `STLocalMaxgL`), so the net owed change is +2. This is required by the ticket's own instance list (§5 above) and allowed by DECISIONS §20 (1) (append-only registry lines in a writable `Axioms.lean`). It is reported as T2269c for the dispatcher to note. Not a RETURN. When merging, the hub should take the union if T2265's `Axioms.lean` edit conflicts (§20 (3)).
- O2. The prove report's owed counts (155 → 157) and mine (154 → 156) come from different counting scripts. The difference (+2) agrees.
