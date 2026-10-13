Auditor model: claude-opus-5-5
# T2486b audit (U2-BA part (b): `RBM3D/BA/B45BA.lean`, targets 6-8), round 1
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2486b-audit1`, detached at `t/T2486b` 3b47302c. Ticket `docs/tickets/T2486.md` + Amend 1
(Amend 1 touches target 2 (c) only, part (a)). Report written Tue Oct 13 06:28 UTC 2026 (`date -u`).

## Verdicts
| target | declaration(s) | verdict |
|---|---|---|
| 6 | `baZeroModeGen_kerSums`, `baB45Gen_facts` | PASS |
| 7 | `baWardTypePgL_of`, `baB45gL_of` | PASS |
| 8 | `BAWardTypePPin`, `BAB45Pin`, `baWardTypePPin_holds`, `baB45Pin_holds` | PASS |

## 1. Diff and sole writable files
```
$ git diff --name-status main...t/T2486b
M	RBM3D.lean
A	RBM3D/BA/B45BA.lean
$ git diff main...t/T2486b -- RBM3D.lean   (changed lines)
+import RBM3D.BA.B45BA
$ grep -n "^import" RBM3D.lean | tail -2 ; tail -1 RBM3D.lean
582:import RBM3D.Graph.BAExp14a2
583:import RBM3D.BA.B45BA
#assert_rbm_axioms
$ G1: git diff main...t/T2486b --stat -- RBM3D/Chain RBM3D/Induction RBM3D/Loop RBM3D/Test | wc -l
       0
$ grep -rln "import RBM3D.BA.B45BA" RBM3D RBM3D.lean
RBM3D.lean
```
Both files are sole writable files (`RBM3D/BA/B45BA.lean`; `RBM3D.lean` import lines). No merged file edited; `Test/Axioms.lean`
untouched (registry edits are part (a) only, per ticket).

## 2. Statements against the binding pins (Lean-checked)
Scratch file `AuditPins.lean` = `import RBM3D.BA.B45BA` + the check file's lines 262-284 verbatim (`T2486_BAKerSums`, `T2486_BAB45Facts`,
`T2486_BAWardTypePPin`, `T2486_BAB45Pin`) + the check file's target-7 shape (lines 297-301) as a named def, then:
```
example (d : ℕ) : T2486_BAKerSums d := baZeroModeGen_kerSums d
example (d : ℕ) : T2486_BAB45Facts d := baB45Gen_facts d
example (d : ℕ) : T2486_BAWardTypePPin d := baWardTypePPin_holds d
example (d : ℕ) : T2486_BAB45Pin d := baB45Pin_holds d
example (d : ℕ) : T2486_BAWardTypePPin d = BAWardTypePPin d := rfl
example (d : ℕ) : T2486_BAB45Pin d = BAB45Pin d := rfl
example : T2486_Target7Shape := fun d hd sz κ ε 𝔠 𝔡 Cd z s t hκ hf hs ht hN hD =>
  ⟨baWardTypePgL_of d hd sz κ ε 𝔠 𝔡 Cd z s t hκ hf hs ht hN hD, baB45gL_of d hd sz κ ε 𝔠 𝔡 Cd z s t hκ hf hs ht hN hD⟩
$ lake env lean scratchpad/T2486b/AuditPins.lean ; echo exit=$?
(only the #print axioms lines of §4)
exit=0
```
Target 7's hypothesis list is exactly the shape's (positional application, no extra binder): `3 ≤ d`, `0 < κ`, `BAFlow`, `0 ≤ s`,
`t < 1`, eventual `N⁻¹ ≤ 1 - t_n`, `STGdecayWgL` (T1-BA's pin). Target 8's pins are definitionally the check pins (`rfl`), every `R`.
Target 6 (`B45Gen_Facts`, `Chain/B45Gen.lean:61`) and target 8 (`STIngRgL`, `Chain/Step34Gen.lean:373`) are merged generic texts at the
BA tuple `(seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)`, quantifier order unchanged (`∀ κ, 0 < κ → ∃ C₆ …` and `3 ≤ d → ∀ κ ε 𝔡 … ∃ 𝔠d …`).
```
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2486-check.lean   # in the audit worktree
exit=0   ; grep -c error -> 0
```

## 3. Vacuity, hidden hypotheses, cycles
- No new `structure`/`class`; the two new `def`s are the pins themselves. X1-C4 grep (§5) 0: no second named `Prop`.
- `baWardTypePPin_holds`/`baB45Pin_holds` split `by_cases 3 ≤ d`; the `d < 3` branch closes because `STIngRgL` begins with `3 ≤ d →`
  (merged text, `Step34Gen.lean:374`), i.e. those `d` are vacuous by the merged pin, not by this file. At `d = 3` the proof is
  `stWardTypePPingL_of`/`stB45PingL_of` with merged inputs `baStep5CasesGen_flowFacts`, `baB45Gen_facts`, `baKcalDecay_holds`.
- Dependencies are merged (part (a) 7be99aae on main: `baZeroModeGen_wardCls`, `baKcalDecay_holds`, `baStep5CasesGen_flowFacts`;
  `Chain/B45Gen` 78f4cc14) or proved in this file. The imports are `Chain.B45Gen`, `Chain.Step2Kern`, `BA.SEforLnBA`, `BA.KKernel`,
  `BA.KBase`, `BA.Ward`; nothing imports `B45BA` but `RBM3D.lean`: no cycle.
- No external hypothesis is introduced. `0 < g₀` is not read (target 6 uses `BAflow_real` at each `n`): the `∀ n` fields hold at every `n`.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.B45BA 2>&1 | grep -E "error|^warning|Build completed" | tail -2
warning: RBM3D/BA/B45BA.lean:29:100: This line exceeds the 100 character limit, please shorten it!
Build completed successfully (4099 jobs).
$ lake build > full.log ; echo exit=$? ; grep -cE "error:" full.log ; tail -2 full.log     # full library, runs #assert_rbm_axioms
exit=0
0
non-vacuity certificates: 0 of 123 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4354 jobs).
$ #print axioms (AuditPins.lean)
'RBM.BA.baZeroModeGen_kerSums' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baB45Gen_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardTypePgL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baB45gL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baWardTypePPin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baB45Pin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.B45BAInst.inst_kerSums' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.B45BAInst.inst_b45Facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.B45BAInst.inst_wardTypePgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.B45BAInst.inst_b45gL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.B45BAInst.inst_wardTypePPin_applied' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.B45BAInst.inst_b45Pin_applied' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|^ *axiom " RBM3D/BA/B45BA.lean | wc -l
       0
```
Warnings: only `longLine` on the module docstring.

## 5. Ticket greps (on `RBM3D/BA/B45BA.lean`)
```
C1   grep -nE '\|E\||norm_mE|mSigma|SB d|zt E|etaT|STFlow|STflowE|seqHflow [^B]|lemT' | wc -l      -> 0
     grep -n withLam | grep -v 'seqP (sz.withLam 0)\|seqP (sz0.withLam 0)'
     17:`(law, Flow, mk, T0) = (seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)`.  No merged file is edited.   (docstring)
UBA-C1 grep -nE 'gK|≤ A \*' | wc -l                                                            -> 0
TN-C4  grep -n STGridRepNgL | wc -l                                                            -> 0
X1-C4  grep -nE '(def|abbrev|structure) (ZeroModeGen_WardCls|…|Step5CasesGen_FlowFacts)' | wc -l -> 0
C6     grep -cE 'KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|KLK_two|KLnodes|TSP'                         -> 0
```

## 6. Compiled nonempty instances (same file, namespace `RBM.BA.B45BAInst`)
Data: `d = 3`, merged `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`
(`BA/FlowPins`), `s ≡ 1/2 < t ≡ 2/3`, `t ≤ BAflowT0` by `t0_sz0`, `C_d = 1`; `N⁻¹ ≤ 1/3` at every `n` proved (private
`B45BAInst_inv_size`, `N = (W L)^3 ≥ 3`). All compiled in the module build above.
| target | instance | hypotheses left | deterministic premises discharged |
|---|---|---|---|
| 6 KerSums | `inst_kerSums (n)` | none | `0 < κ`, `BAFlow` |
| 6 Facts | `inst_b45Facts`; two `example`s: row sum `(+,-)` and column sum `(-,-)` at `n = 0`, `t = 1/2`, bound `1/(1-1/2)` (`C₆ = 1`) | none | as above, `0 ≤ t < 1` |
| 7 | `inst_wardTypePgL`, `inst_b45gL` | `STGdecayWgL` (T1-BA pin) | `3 ≤ 3`, `κ`, `BAFlow`, `0 ≤ s`, `t < 1`, `N⁻¹ ≤ 1 - t_n` (all `n`) |
| 8 | `inst_baWardTypePPin`, `inst_baB45Pin` (`d = 3`, `R = STAny`); `inst_wardTypePPin_applied`, `inst_b45Pin_applied` | `STLKgL`, `STStep2ConclgL` (premises of the merged `STIngRgL`, other gates' pins) | `3 ≤ d`, `κ, ε, 𝔡 > 0`, `C_d = 1 > 0`, `BAFlow`, `s < t ≤ T0`, `R` (`trivial`), `STKboundgL` (`baKbound_holds`), `STKwardgL` (`baKward_holds`), `STConStInd` (`s1Setup_conStInd_const`) |
No `N = 0`, empty index, collapsed window (`1/2 < 2/3 < 1`) or `False` premise; the `_applied` instances open the existential `𝔠d` and
feed the pin a full premise list at concrete data, so the pins are not vacuous at `d = 3`.

## 7. Paper deltas
- `docs/paper-deltas.md` on main: no `T2486` entry yet (numbering at merge, ticket answer (6)).
- Statement differences of part (b): the pins and `B45Gen_Facts` are the merged generic texts at the BA tuple (identical to the binding
  pins, §2). One Lean/paper difference: `BAWardTypePPin`/`BAB45Pin` are stated for every `d`, vacuous for `d < 3` (paper `d ≥ 3`):
  proposed as `T2486f` in `T2486b-prove.md` (d). The route difference for `C₆ = 1` (resolvent identity instead of the entrywise comparison
  of `(eq:THETAinftinf)`) is proposed as `T2486e` (no statement change). The cactus far decay (`T2486a`) belongs to part (a).
Coverage complete.

## 8. Observations (no RETURN)
- O1. The instance theorems `inst_*` are public names inside namespace `RBM.BA.B45BAInst` (stem in the namespace, not in the
  declaration name); clash grep in the prove report and the full build show no collision. Same pattern as merged instance namespaces.
- O2. Target 6 uses one argument (translation invariance + symmetry via `BAMB_shift`, `BAMB_symm`) for all four charge pairs instead of
  the ticket's mixed/equal split; the statement is unchanged and dispatcher answer (3) names these two lemmas.

## Final
Targets 6, 7, 8: PASS. No dispatcher sign-off needed.
