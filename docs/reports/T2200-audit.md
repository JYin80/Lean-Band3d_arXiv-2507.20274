Auditor model: claude-opus-5-5

# T2200 audit (round 1) — ST2-13b `Path/DifREP3` — Mon Oct  5 19:19:31 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2200-audit1`, detached at `t/T2200` = `afb1467` (parent `9a207a1` = main).
Scratch: `scratchpad/T2200/` (`sdiff.py`, `AuditCheck.lean`, `RootSim.lean`).

## 1. Diff scope, forbidden tokens
```
$ git diff --name-only main...t/T2200
RBM3D/Path/DifREP3.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2200 -- RBM3D/Test/Axioms.lean   (only hunk)
-   `RBM.Gauss.Sizes.STGridRepN, -- `Sol_CalL` + `lem:DIfREP` on the grid, every loop length ...
-   `RBM.Ind.GridRepWTailNAt, -- clause (iii) / (iv) of `STGridRepNAt` for `difRepMartN`: ST2-13 (T2168)
$ git diff main...t/T2200 | grep -nE '^\+.*\b(sorry|admit|native_decide)\b|^\+\s*axiom '; echo grep_exit=$?
grep_exit=1
```
Exactly the two sole writable files; exactly the two owed registry lines deleted; no frozen signature touched.

## 2. Statements against the pin (check file section 2), by script
```
$ python3 scratchpad/T2200/sdiff.py   (whitespace-normalised text of def blocks / theorem types vs `…Stmt` bodies)
uKerQ vocab identical: True
STeeUQM vocab identical: True
GridRepWTailQNAt vocab identical: True
STeeUQM_empty == STeeUQMEmptyStmt : True
gridRepWTailN_of_Q == GridRepWTailNOfQStmt : True
zeroModeSet_UN_eq_uKerQ == ZeroModeSetUNEqUKerQStmt : True
difRep3_UN_transfer == DifRep3UNTransferStmt : True
gridRepWTailQN_holds == GridRepWTailQNHoldsStmt : True
gridRepWTailN_holds == GridRepWTailNHoldsStmt : True
stGridRepN_holds == StGridRepNHoldsStmt : True
$ lake env lean scratchpad/T2200/AuditCheck.lean
  (import RBM3D + RBM3D.Path.DifREP3; check-file sections 1-2 verbatim; then for each of the 7 targets
   `example : T2200Check.<X>Stmt := @<target>`)
exit=0   (no error line; the only output is the section-1 #check lines and the lines in §4 below)
```
Pin content (read against the ticket): `GridRepWTailQNAt` keeps clause (iv)'s order
`κ ε 𝔡 → 𝔠 sz z (STFlow) → s t → D>0 → ∃ CK ≥ 0 → ∀ K (K n ≠ 0, N^CK ≤ K n eventually) → ∀ ε'>0 → ∀ᶠ n → ∀ i`,
maximal form `∃ k ≤ K n` inside `pathP`, floor `N^{-D}` inside the square root, kernel
`zeroModeSet Q ∘ UN(u_j,u_k)`, proxy `STeeUQM … (u_j) (u_k) … Q`; `N → ∞` is not a premise (taken from `STFlow`,
`hz.1.2.2.1` in the proof). Targets 1-6 carry no `3 ≤ d`; target 7 carries `3 ≤ d` only (as pinned).
`CK` returned by target 5 (file :2345): `refine ⟨9 * (m : ℝ) + 3 * D + 22, by positivity, ?_⟩` — chosen before
`K`, `ε'` and independent of `Q`, `κ`, `ε`; equals the ticket's allowed variant value (step (e) variant, `9m + 3D + 22`).

## 3. Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`; the three vocabulary items are a kernel, a finite sum and a `Prop` copied verbatim
  from the check file. The only hypotheses of target 5 are those of the pin.
- Dependencies are merged, public on `main` (`#check` output of the check file, section 1, in the audit run):
```
RBM.Ind.gridRepTailN_holds : ∀ (d m : ℕ), 2 ≤ m → RBM.Ind.GridRepTailNAt d m
RBM.Ind.stGridRepN_of_tails : ∀ (d : ℕ), 3 ≤ d → (∀ (m : ℕ), 2 ≤ m → RBM.Ind.GridRepTailNAt d m) →
      (∀ (m : ℕ), 2 ≤ m → RBM.Ind.GridRepWTailNAt d m) → RBM.Gauss.Sizes.STGridRepN d
$ git log --oneline -1 main -- RBM3D/Path/DifREP2.lean RBM3D/Path/DifREP1.lean
76b840e T2180: merge ST2-13a Path/DifREP2 (STGridMart unconditional)
```
- Imports: `RBM3D.Path.DifREP2`, `RBM3D.Induction.ZeroModeCalc`, `RBM3D.Induction.GridDuhamelN` (not `RBM3D`); no cycle.
- No external hypothesis introduced (no limit check needed). Target 7 is `stGridRepN_of_tails d hd
  (gridRepTailN_holds d) (gridRepWTailN_holds d)` — no premise left.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Path.DifREP3
✔ [3855/3855] Built RBM3D.Path.DifREP3 (19s)
Build completed successfully (3855 jobs).
$ lake env lean scratchpad/T2200/AuditCheck.lean   (#print axioms; collectAxioms over every constant of module RBM3D.Path.DifREP3)
'RBM.Ind.STeeUQM_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridRepWTailN_of_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.zeroModeSet_UN_eq_uKerQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.difRep3_UN_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridRepWTailQN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.gridRepWTailN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.stGridRepN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.DifREP3Inst.inst_gridRepWTailQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.DifREP3Inst.inst_gridRepWTailN' depends on axioms: [propext, Classical.choice, Quot.sound]
DifREP3 declarations: 183, with a non-standard axiom: 0
$ registry pre-check: RBM3D.lean with `import RBM3D.Path.DifREP3` after its last import (line 241), Test/Axioms rebuilt
$ diff RBM3D.lean scratchpad/T2200/RootSim.lean
241a242
> import RBM3D.Path.DifREP3
$ lake build RBM3D.Test.Axioms  -> Build completed successfully (2 jobs).
$ lake env lean scratchpad/T2200/RootSim.lean; echo exit=$?
exit=0
1:axiom audit: 5895 theorems, 2084 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ grep -cE "GridRepWTailQNAt|GridRepWTailNAt|STGridRepN\b" rootsim.log
0
```
The full `lake build` is the hub's at merge.

## 5. Compiled nonempty instances (namespace `RBM.Ind.DifREP3Inst`, file :2386-2565, compiled by the build above)
| target | instance | data |
|---|---|---|
| 1 `STeeUQM_empty` | `example` :2417, :2454 | `sz0`, `n = 0`, `E = 1/2`, `v = 0`, `w = 1/16`, `σ = (+,−,+)`, `a = 0`, `H = 0` and `H = 1` |
| 2 `gridRepWTailN_of_Q` | `example : GridRepWTailNAt 3 2` :2519 | premise discharged by target 5 at `Q = ∅` |
| 3 `zeroModeSet_UN_eq_uKerQ` | `example` :2427, :2462 | `L = 4`, `g = lam 0`, `Q = {0}`, `A ≡ 1` and `A b = (b_0)_0` |
| 4 `difRep3_UN_transfer` | `example` :2437, :2470 | `v = 1/32`, `w = 1/16`, `k = 4`, `u_j = gridTime 0 (1/16) 4 j`, `A_j ≡ 1` and `A_j b = j + (b_0)_0`; `3 ≤ L`, `|E| ≤ 2`, `0 ≤ v,w < 1` by `sz0.three_le_L`, `norm_num` |
| 5 `gridRepWTailQN_holds` | `inst_gridRepWTailQN` :2488; `example`s :2515-2516 at `(m,Q) = (2,{0}), (3,∅)` | `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`, `D = 1`, `ε' = 1/10`, `K n = ⌈N_n^CK⌉₊ + 1` (`≠ 0`, `≥ N^CK` discharged) |
| 6 `gridRepWTailN_holds` | `inst_gridRepWTailN` :2522; `example`s :2549-2550 at `m = 2, 3` | as for 5 |
| 7 `stGridRepN_holds` | `example : STGridRepN 3` :2553; `STGridMart 3` :2556; `STStep2 3` :2561 via `ST_step2_of_pinsN'` | `STNewKLK 3`, `STLWT 3`, `STEMn2Exp 3`, `STOptL2 3`, `STLocalAvgOfL2 3` stay hypotheses (other gates' pins, CLAUDE.md §4 step 2) |

Every deterministic hypothesis is discharged at concrete data; no `N = 0`, empty index, collapsed window
(`t − s = 1/16`, `gridStep_inst : … = 1/64`) or `False` premise; `K n` is polynomial in `N_n`, not an
astronomical witness chosen to make the claim vacuous (the pin quantifies over every such `K`).

## 6. Paper-delta coverage
Prove report (d) proposes `T2200a`–`T2200e`: uniformity in `k ≤ K` by the coarse time grid and the exact
transfer (a); the `Q^{(A)}∘𝒰` form with proxy `(Q∘𝒰 ⊗ Q∘𝒰̄)∘(ℰ⊗ℰ)` and no case condition (b); the second-order part
by Doob per `(p,a')` and `CK = 9m+3D+22`, `C' = 4m+D+6` depending on `m, D` only (c); the proxy shifts
`u_{j+1} → u_j` and `(u_j,v_p) → (u_j,u_k)` (d); every `d`, `STGridRepN` unconditional for `d ≥ 3`, `C₀ = m+9` (e).
This covers every Lean/paper difference the ticket lists (with (c) stating the variant actually used instead of the
`T_w P_u` factorisation). `grep -c T2200 docs/paper-deltas.md` → `0` (to be appended by the dispatcher).

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
1. With `Q = {0}` a tensor constant in slot 0 lies in the kernel of `projMat`, so the `A ≡ 1` instances of targets 3
   and 4 (:2427, :2437) are very likely `0 = 0`; the second instances with `A b = (b_0)_0`, `A_j b = j + (b_0)_0`
   (:2462, :2470) are non-constant in slot 0 and are the ones that count. Likewise target 1 at `H = 0` vs `H = 1`.
2. Section (a) row 5 tabulates route (e) (`CK = 5m+2D+16`); the proof uses the ticket's allowed variant
   (`CK = 9m+3D+22`), stated in Narrative 2 and (d). No (a′) was written; the variant's value is within the ticket.
3. Public non-target helpers `hs0`, `hst`, `htT`, `gridStep_inst`, `σ3`, `a0`, `inst_*` are in the instance
   namespace `RBM.Ind.DifREP3Inst` that the ticket designates.

## Verdict
| target | verdict |
|---|---|
| 1 `STeeUQM_empty` | PASS |
| 2 `gridRepWTailN_of_Q` | PASS |
| 3 `zeroModeSet_UN_eq_uKerQ` | PASS |
| 4 `difRep3_UN_transfer` | PASS |
| 5 `gridRepWTailQN_holds` | PASS |
| 6 `gridRepWTailN_holds` | PASS |
| 7 `stGridRepN_holds` | PASS |
| registry `Test/Axioms.lean` (two owed lines deleted; pre-check exit 0) | PASS |

**T2200: PASS.** No dispatcher sign-off needed. Hub: add `import RBM3D.Path.DifREP3` after the last import of
`RBM3D.lean` at merge.
