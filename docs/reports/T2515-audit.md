Auditor model: claude-opus-5-5
# T2515 row a audit (BA/GUEKPrim; D1, targets 1-8) — round 1, Thu Oct 15 09:11:46 UTC 2026

Branch `t/T2515` at ed3c0873 (base `main` 0deabaa8); audit worktree `../RBM3D-wt/T2515-audit1` (detached). Row b
(`BA/GUEEntry`, `t/T2515b`) is out of scope. Scratch: scratchpad `T2515/AuditCheck.lean`, `c1.py` (uncommitted, not in the repo).

## 1. Build and axioms
```
$ lake build RBM3D.BA.GUEKPrim      # 09:08:48-09:09:03 UTC; GUEKPrim.olean written 09:09 UTC in the audit worktree
exit 0; `^error` lines: 0; warnings in RBM3D/BA/GUEKPrim.lean: 0
Build completed successfully (3929 jobs).
$ lake env lean <scratchpad>/T2515/AuditCheck.lean   (#print axioms part)
'RBM.Univ.UNOUProfile.ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNOUProfile.ba_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThetaTransfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baT0Cmp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThetaTilde_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThetaTilde_osc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baThetaDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baOUProfRowk_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProfComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNOUProfile.ba_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kTwoGUEBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kTwoGUELoopBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kTwoGUEBA_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kTwoGUEBA_eq_ThetaTilde' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.hasDerivAt_kTwoGUELoopBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueK_existsBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kTwoGUEBA_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kTwoGUEBA_bridge_pm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kTwoGUEBA_bridge_pp' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' RBM3D/BA/GUEKPrim.lean   -> 0
$ wc -l RBM3D/BA/GUEKPrim.lean   -> 1241   (stop line 1,500; binding 2,000)
```

## 2. Statements against the signed texts (1a-audit §4, check Part 2, probe D1 (iv) texts)
`AuditCheck.lean` = `import RBM3D.BA.GUEKPrim` + check Part 2 (`namespace RBM.BA.T2515Check`, copied by `sed`) + the probe's
`T2515_KBridgeBA`, `T2515_KDerivBA` verbatim (by `awk`, now reading the committed `kTwoGUEBA`/`kTwoGUELoopBA`) + these lines:
```
example (d : ℕ) : T2515_ProfSpec d (UNOUProfile.ba d) := UNOUProfile.ba_spec d
example : T2515_ThetaTransfer := baThetaTransfer
example : T2515_CmpBA := baT0Cmp
example : T2515_ThetaTildeOscBA := baThetaTilde_osc
example : T2515_ThetaDiffBA := baThetaDiff
example (d : ℕ) : T2515_ProfZero d := UNOUProfile.ba_zero d
example (d : ℕ) : T2515_KBridgeBA d (fun ζ => 0 ≤ ζ ∧ ζ ≤ 1) := kTwoGUEBA_bridge d
example (d : ℕ) : T2515_KDerivBA d := hasDerivAt_kTwoGUELoopBA d
theorem aud_eq (d) (P) (hP : T2515_ProfSpec d P) : P = UNOUProfile.ba d := (cases P; funext; ba_spec)
example (d : ℕ) : T2515_ProfRowBA d := fun hd P hP => (aud_eq d P hP) ▸ baOUProfRowk_holds d hd
example (d : ℕ) : T2515_ProfCompBA d := fun P hP => (aud_eq d P hP) ▸ baProfComp d
example : ∀ d : ℕ, 3 ≤ d → UNOUProfRowk (UNKind.ba d) (UNOUProfile.ba d) := baOUProfRowk_holds
example (d : ℕ) : RBG_ProfComp (UNKind.ba d) (UNOUProfile.ba d) := baProfComp d
example : T2515_CmpBA := baThetaTransfer          -- negative control
$ lake env lean <scratchpad>/T2515/AuditCheck.lean ; echo exit $?
AuditCheck.lean:107:25: error: Type mismatch      (the negative control only; no other error line)
  baThetaTransfer has type ∀ (d L : ℕ) [inst : NeZero L] (lam : ℝ) (z : ℂ), 0 < z.im → ... but is expected to have type T2515_CmpBA
exit 1   (19 `#print axioms` lines as in §1)
$ diff <(awk '/^def kTwoGUEBA/,…' Probe/T2515Pins.lean) <(awk … BA/GUEKPrim.lean) && echo IDENTICAL        -> IDENTICAL
$ diff (same for kTwoGUELoopBA)                                                                          -> IDENTICAL-Loop
```
Every signed text is matched at definitional type by the committed declaration; targets 4, 5 conclude the merged
`UNOUProfRowk`, `RBG_ProfComp` at exact type. Merged signatures read (not restated): `UNOUProfile` (`OUInterfaceK:43`, fields
`pm`, `pp` only), `UNOUProfRowk` (`:56`: `∃ C` before `sz`, `0 ≤ ζ ≤ 1`, `C (lam²)⁻¹ / W^d`, `K.bulk`), `RBG_ProfComp`
(`RandomLayerBG:123`), band `gueK_exists` (`KPrim:749`: same three clauses; BA start `BAKsol … t₁` in place of `KLgen`).

Per-target statement verdicts:
| # | target | statement check | verdict |
|---|---|---|---|
| 1 | `UNOUProfile.ba`, `_spec` | `= T2515_ProfSpec` (rfl), `W^{-d}(Θ̃_ζ M^{(+,σ)})`, `S̃_ζ = SBtilde d L 0 ζ` | PASS |
| 2 | `baThetaTransfer`, `baT0Cmp` | `= T2515_ThetaTransfer`, `= T2515_CmpBA`; all `lam`, `s`, `σ₁ σ₂`; `∃ cT` before `d L lam z` | PASS |
| 3 | `baThetaTilde_eq`, `baThetaTilde_osc` | osc `= T2515_ThetaTildeOscBA` (all `ζ ∈ [0,1]`, `∃ C` before `L lam z`, `C (lam²)⁻¹`, no `W^τ`); `_eq` unpinned identity (BAReal, `0 ≤ t₀ < 1`, `0 ≤ ζ ≤ 1`) | PASS |
| 4 | `baOUProfRowk_holds` | exact `∀ d, 3 ≤ d → UNOUProfRowk (UNKind.ba d) (UNOUProfile.ba d)`; implies `T2515_ProfRowBA` | PASS |
| 5 | `baProfComp` | exact `RBG_ProfComp (UNKind.ba d) (UNOUProfile.ba d)`; implies `T2515_ProfCompBA` | PASS |
| 6 | `baThetaDiff`, `UNOUProfile.ba_zero` | `= T2515_ThetaDiffBA` (consumer form of `queRowDiff`), `= T2515_ProfZero` | PASS |
| 7 | `kTwoGUEBA`…`gueK_existsBA`, bridges | defs identical to the signed probe text; `= T2515_KDerivBA`; bridge `= T2515_KBridgeBA d (0 ≤ ζ ≤ 1)` | PASS |
| 8 | instances | §4 | PASS |

## 3. Vacuity, hidden hypotheses, cycles
- No new `structure`/`class`; `UNOUProfile.ba` is a `def` with two fields (no `Prop` field). No target carries an unproved `Prop`
  premise: premises are `3 ≤ d`, positivity/window/bulk, `BAReal`, `0 ≤ t₁ ≤ t₀ < 1`, `[NeZero L/W]`, `3 ≤ L`.
- `gueK_existsBA` start `BAKsol` (`FlowPins:283`, `Classical.choice` of an `IsKLoopS` solution, `0` fallback): non-vacuous,
  since `baKsolve : ∀ d, BAKsolve d` (`KTreeRep:1699`) proves existence and `baKsol_two` (`KInduct:88`, premises `0 < κ`, `0 < g`,
  `3 ≤ L`, `BAReal`) identifies its 2-loops — exactly the extra premises `hg hκ hL hr` of `gueK_existsBA`.
- Dependencies are merged on `main` (no V module): `grep -cE '^import RBM3D.BA.(MainInd|TwistPins|Step6)' GUEKPrim.lean -> 0`;
  imports: `RandomLayerBGBA, Prop6Path, KBase, KTreeRep, KInduct, EMn2BA, EKNonzero, GUEPhase.KPrim, OUInterfaceK`
  (`KInduct` added to the ticket's list; merged). No importer besides `RBM3D.lean`. No external hypothesis (no limit check due).
- X1-C4 `(def|abbrev|structure) (UNOUProfRowk|RBG_ProfComp|BAProp8|BAprof|GUEEntryMix|SBtilde)\b` -> 0.
- C1 regex on the 20 public statements (`c1.py`, comments stripped, `\bTheta d\b`, `SB d L` with `g ≠ 0`, band `kTwoGUE`/`KLgen`,
  `UNModel.band`, `msc|mE|lemT|lemE`, `2 - κ`, `‖m‖ = 1`): `public statements scanned: 20 C1 hits: []`.

## 4. Compiled nonempty instances (namespace `RBM.BA.GUEKPrimInst`, `GUEKPrim.lean:1128-1237`, compiled in §1's build)
```
examples: 23. Per endpoint (script count of `example` lines naming it):
UNOUProfile.ba_spec:3 baThetaTransfer:2 baT0Cmp:1 baThetaTilde_eq:3 baThetaTilde_osc:1 baThetaDiff:1 baOUProfRowk_holds:1
baProfComp:3 UNOUProfile.ba_zero:1 kTwoGUEBA_self:1 kTwoGUEBA_eq_ThetaTilde:1 hasDerivAt_kTwoGUELoopBA:2 gueK_existsBA:1
kTwoGUEBA_bridge:1 kTwoGUEBA_bridge_pm:1 kTwoGUEBA_bridge_pp:1
```
Data: `d = 3`; `S0 = clsS 4 _ UNPins_hg_3_10` (`UNPins:884`, `L = 4`, `lam = (fp 4 _).g0 ∈ (0, 3/10]`), `n = 0`,
`zS0 = ⟨E_*, 1/2⟩`, `𝔡 = 1/10` (window `S0_win` proved), `κ = clsκ 4 _ > 0` (`clsκ_pos`), bulk `cls_bulk 4 _ _`; target 4 and
the oscillation at `ζ ∈ {0, 1/2, 1}`; flow-point data `MFixedPointInst.P : FlowPt 4 10` (`P.real : BAReal …`) at `t₀ = 1/2`,
`ζ ∈ {0, 1/2, 1}`; (7.33) on `t₁ = 1/4 ≤ t = 1/2`, both charge pairs; `gueK_existsBA 3 4 32` at `fp 4 _`, `t₁ = 1/4`, `t₀ = 1/2`,
`n0 = 4`. Every deterministic premise is discharged; only `UNG1Rowk`, `UNG2bRowk` (N2/C5 pins) stay hypotheses, of the
`ouRowk_of_pins` example. No `N = 0`, empty index, collapsed window, `False` premise, or large witness. PASS.

## 5. Diff and registry
```
$ git diff --name-status main...t/T2515
M RBM3D.lean   A RBM3D/BA/GUEKPrim.lean   A RBM3D/Probe/T2515Pins.lean   M RBM3D/Test/Axioms.lean
```
All four are sole writable files (probe: branch only, never merged). `RBM3D.lean`: one line `import RBM3D.BA.GUEKPrim` after the
last import, `#assert_rbm_axioms` still last. `Test/Axioms.lean`: `UNG1Rowk` comment adds C3 (`baProfComp`, T2515); `UNOUProfRowk`
removed from `owedProps` and added to `structuralProps` naming both instances (DECISIONS §337 (4)). No merged declaration changed.
`private`/stem rule (E): all helpers are `private GUEKPrim_*`; public names are the ticket's targets; `zS0` in `GUEKPrimInst`.

## 6. Paper deltas
`grep -c T2515 docs/paper-deltas.md` -> 0 (expected before merge). Prove report §(d) proposes `T2515a` (BA OU profile
`W^{-d}(Θ̃_ζ M)`, `S̃_ζ = SBtilde d L 0 ζ`), `T2515b` (lossless BA `thetaDiff`/`UNOUProfRowk`, `C λ⁻²` vs the paper's `≺ λ⁻²`,
`1_2:535-537`), `T2515c` (matrix-valued BA GUE-phase 2-loop with row-sum shift; `gueK_existsBA` premises `0 < g`, `0 < κ`, `3 ≤ L`).
These cover every Lean/paper difference of row a found here (the transfer and `cT` comparison restate merged flow-point facts).

## 7. Observations (no statement, instance, build, axiom or paper-delta effect)
1. Merge with current `main` dec8e150: `git merge-tree --write-tree main t/T2515` reports CONFLICT (content) in `RBM3D.lean` and
   `RBM3D/Test/Axioms.lean`. Cause: T2514/T2516 merges added the import lines `BA.MAPins`, `MALocal`, `MATrLocalBA`, `MAQDiff`
   at the same spot and edited the adjacent `UNLocAvgk` `structuralProps` line. Both are line unions (the ticket's sibling scan);
   the hub must bring in `GUEKPrim.lean` plus exactly the T2515 hunks (import line; `UNG1Rowk` comment; `UNOUProfRowk` move) on top
   of current `main`, not the branch's copies of the two shared files.
2. The prove report is 288 lines: within CLAUDE.md §6's 300, above the ticket's 250.
3. `baThetaDiff`'s proof constant (`4C₈/cT + 4𝔡⁻²`) differs from section (a)'s `2C₈/cT + 𝔡⁻²`; the statement is `∃ C` (§(b) item 5).

## Verdict
Targets 1-8 (row a): **PASS**. No dispatcher sign-off needed. Hub: resolve observation 1 by line union at merge.
