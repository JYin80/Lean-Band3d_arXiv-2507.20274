Auditor model: claude-opus-5-5
# T2501 row a2 audit (round 1) — Wed Oct 14 03:21:13 UTC 2026
Branch `t/T2501a2` @ 3f8e9624 (merge-base 84915e5f); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2501a2-audit1` (detached).
Scope: target 2 `baIniTermGen_cltFlow` (= `T2501_CltFlowBA`), its five registry-head producers, instance 8 for target 2, registry edits. Rows a1/b are not audited here.

## 1. Statement against the pin (script)
Scratch file (uncommitted): `T2501-check.lean` + `import RBM3D.BA.CltFlowBA` + the lines below, compiled in the audit worktree.
```
example : T2501_CltFlowBA := baIniTermGen_cltFlow
example : <check shape 1: ∀ d, 3 ≤ d → ∀ κ ε 𝔠 𝔡, 0<κ → 0<𝔡 → ∀ sz z, BAFlow … → STThPropsg (baFMz sz z)> := baSTThPropsg_holds
example : <check shape 2: … STReg5I sz s t → STKpropsg … s ∧ STMfarg … s ∧ STKfargL … s> := ⟨baSTKpropsg_holds …, baSTMfarg_holds …, baSTKfargL_holds …⟩
example : <check shape 3: CltRepg … (g₀•PsiI) (fun _ => 0) (BAflowEs sz z) ∧ CltInvg …> := ⟨baCltRepg_holds sz z, baCltInvg_holds sz z⟩
$ lake env lean $S/pinchk.lean > pinchk.out; echo exit=$?; grep -c error pinchk.out
exit=0
0
```
Lean statement (`CltFlowBA.lean:566`):
```
theorem baIniTermGen_cltFlow (d : ℕ) : IniTermGen_CltFlow d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
```
Pin (`T2501-check.lean:251-253`): `∀ d : ℕ, IniTermGen_CltFlow d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0`.
Identical up to the binder of `d`; `example : T2501_CltFlowBA := baIniTermGen_cltFlow` elaborates by `rfl`. The class body (`CltFarUGen.lean:62-73`, merged, unchanged)
keeps `3 ≤ d → ∀ κ ε 𝔡 > 0, ∃ κ' δ` before `(𝔠, sz, z)`, the `t`-free fields, and the `∀ s t` block under `STReg5I`; tuple = ticket's BA tuple.
Producers (heads of the five deleted registry lines) have hypotheses `3 ≤ d`, `0 < κ`, `0 < 𝔡` (+`0 < ε` for `STKfargL`; `STReg5I`, `0 ≤ s < t ≤ T0` for
`STKpropsg`), each a subset of the check shapes' binders (weaker hypotheses than the shape, compiled against it above). `CltRepg`/`CltInvg`: no hypotheses.

## 2. Vacuity, hidden hypotheses, cycles
```
$ F=RBM3D/BA/CltFlowBA.lean; grep counts on $F
sorry/admit/axiom/native_decide: 0
C1 pattern (ticket hypothesis rule): 0
X1-C4 '^(noncomputable )?(def|abbrev|structure) ': 0
local copies 'def (IniTermGen_KerFacts|IniTermGen_CltFlow|STThPropsg|STKpropsg|STIngR5gL)': 0
'T24[0-9][0-9]_' text: 0
withLam other than 'withLam 0': (no lines)
$ grep -n "^import" $F
RBM3D.Chain.CltFarUGen RBM3D.Chain.Step2Kern RBM3D.Evolution.ExpInv RBM3D.Evolution.MeanFar RBM3D.BA.EMn2BA RBM3D.BA.Step2CloseBA
RBM3D.BA.Ward RBM3D.BA.KSolve RBM3D.BA.KTreeRep RBM3D.BA.KInduct RBM3D.BA.Prop6Path RBM3D.BA.TwistStep2 RBM3D.BA.CombesThomas
$ grep -rln "RBM3D.BA.CltFlowBA" RBM3D RBM3D.lean
RBM3D.lean
```
- No structure introduced; all premises are in theorem signatures; the only private `def`s are the instance-(B) data (`:597-606`).
- Every import is a merged module on `main` (new leaf, sole importer `RBM3D.lean`): no cycle. No external hypothesis (every input is a merged proof), so no limit check is required.
- `∀ n` clauses at `g₀ n ≤ 0`: proved without `0 < g₀` (Lean-checked: the theorem has no such premise and `BAFlow` does not give `0 < g₀` at every `n`).

## 3. Compiled nonempty instances (`CltFlowBA.lean:585-765`, `d = 3`)
- (A) `(sz0, zSeq, flow_sz0)`, `(κ,ε,𝔠,𝔡) = (1/2,1/10,1/6,1/10)` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`): target 2 applied, every
  deterministic premise discharged; yields `κ'`, `δ`, `κ' ≤ Im m`, Ward row, `STThPropsg`, `STExpInvgL`; producers `STThPropsg`, `STMfarg`, `STKfargL` (`t ≡ 1/2 ≤ T0`
  by `half_lt_t0`), `CltRepg`, `CltInvg` applied at the same datum.
- (B) `CltFlowBA_szI` (`L ≡ 4`, `W_n = n+25`, `lam ≡ 1`), `z ≡ w − m(w)`, `w = (5003/5000)i`, `(κ,ε,𝔠,𝔡) = (1/70,1/2,1/9,1/10)`, `s ≡ 0 < t ≡ 1/100`:
  target 2 applied with `BAFlow` (`CltFlowBA_flowI`, proved), `STReg5I` (`CltFlowBA_regI`: `1/16 ≤ 99/100`, `1 ≤ 1`), `t ≤ T0` (`CltFlowBA_tI`, via
  `TwistStep2_T0_ge`) all discharged; its full `∀ s t` block (`STMfarg ∧ STGijDecgL ∧ STKfargL ∧ STKpropsg`) is obtained. `baSTKpropsg_holds` applied there too.
- Nondegeneracy: `N_n = (4(n+25))^3 ≥ 10^6 → ∞`; window `s < t` open; no `False` premise; `lam = 1` lies in the Lean `(eq:WO)` range
  `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹` (`Defs/Sizes.lean:177`, `WO`), `L ≡ 4 ≥ 3` is allowed by `Sizes` (`three_le_L`). No astronomically large witness.
- Why two data: at (A) the `STReg5I` window is empty (`Im z_n ≥ 11/30` ⇒ `1 − T0 ≥ 11/36 > lam²`, prove report (a) row 13); (B) supplies a nonempty one.
Instances compile (part of the module build, §4). Verdict for the instance requirement: satisfied.

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.CltFlowBA 2>&1 | grep -E "CltFlowBA|Build completed|error"; echo exit=$?
ℹ [4129/4129] Built RBM3D.BA.CltFlowBA (6.3s)
info: RBM3D/BA/CltFlowBA.lean:768:0: 'RBM.BA.baSTThPropsg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/BA/CltFlowBA.lean:769:0: 'RBM.BA.baSTMfarg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/BA/CltFlowBA.lean:770:0: 'RBM.BA.baSTKfargL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/BA/CltFlowBA.lean:771:0: 'RBM.BA.baCltRepg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/BA/CltFlowBA.lean:772:0: 'RBM.BA.baCltInvg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/BA/CltFlowBA.lean:773:0: 'RBM.BA.baSTKpropsg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/BA/CltFlowBA.lean:774:0: 'RBM.BA.baIniTermGen_cltFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (4129 jobs).
exit=0   (error lines: 0)
$ lake build 2>&1 | grep -E "Build completed|error|registry:|axiom audit"   # whole library on the branch (extra; the hub reruns at merge)
info: RBM3D.lean:608:0: axiom audit: 14964 theorems, 4631 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 114 owed + 123 structural + 7 refuted + 18 superseded; 142 registered premise(s) carry nothing yet: [...]
Build completed successfully (4378 jobs).
exit=0
$ git diff --name-status main...t/T2501a2
M	RBM3D.lean
A	RBM3D/BA/CltFlowBA.lean
M	RBM3D/Test/Axioms.lean
$ git diff --stat main...t/T2501a2 -- RBM3D/Chain RBM3D/Induction RBM3D/Evolution RBM3D/Graph RBM3D/Gauss
(empty)
$ git diff main...t/T2501a2 -- RBM3D.lean   → one line `+import RBM3D.BA.CltFlowBA` after the last import, before `#assert_rbm_axioms`
$ git diff main...t/T2501a2 -- RBM3D/Test/Axioms.lean   (deleted owedProps lines)
-   `RBM.BA.STKfargL, …   -   `RBM.BA.STMfarg, …   -   `RBM.BA.CltInvg, …   -   `RBM.BA.STThPropsg, …   -   `RBM.BA.STKpropsg, …
    + T2455 header: "; `STKfargL`, `STMfarg`, `CltInvg` left this list (concluded by `baSTKfargL_holds`, `baSTMfarg_holds`, `baCltInvg_holds`, BA: T2501)"
    + T2479 header: "; `STThPropsg`, `STKpropsg` left this list (concluded by `baSTThPropsg_holds`, `baSTKpropsg_holds`, BA: T2501)"
```
Owed count 119 → 114 as the ticket's row a2 line requires (prove report's before/after; after confirmed by the build above). The T2462 header note and the
`STStep5ConclgL` owner text are row b's (ticket `:55`), correctly untouched. No merged file or frozen signature changed; the three files are the row's sole writable files.
Name clashes:
```
$ for n in <7 public names> CltFlowBA_; do git grep -lw $n main -- RBM3D | wc -l; git grep -l $n t/T2501 -- RBM3D | wc -l; done
all 0 on main (a6ec5c5c) and on row a1's t/T2501 (0d98bc2b); on the branch only Test/Axioms.lean header notes mention them
```
Merge note for the hub: `main` advanced to a6ec5c5c (T2500) after the merge-base; T2500 also touched `RBM3D.lean` and `Test/Axioms.lean` (other lines); union as the ticket's sibling scan says.

## 5. Paper deltas
The target is the merged class `IniTermGen_CltFlow` at the ticket's BA tuple; the producers' heads are merged pin texts. No new Lean/paper statement
difference is introduced, so no candidate is required; the prove report proposes none, consistent with ticket `:71` (10). The R1 loss `A = (κ+1)/κ` is
inside the existential constants, not in a statement.

## 6. Observations (no statement, instance, build, axiom or paper-delta effect)
- O1. Route differs from the ticket text: `STMfarg` is proved from `baPropM_holds` (`CombesThomas:562`) instead of `baOffDiag_holds` (whose statement is
  not a pointwise decay), adding `import RBM3D.BA.CombesThomas` and `Evolution.MeanFar` beyond the ticket's draft list (ticket `:12`: "the 1a fixes the lists").
  The registry's former owner text for `STMfarg` named `baOffDiag_holds`; the line is deleted, so nothing stale remains.
- O2. Instance (B) is a fixed-`L`, `lam ≡ 1` datum (paper-admissible by `(eq:WO)`, but far from the small-`λ` regime); a genuine growing-`L` datum with a
  nonempty `STReg5I` window was only sketched in (a) (`z' = iη`, `η = N^{-9/10}`), not built. Row b (target 12) cannot reuse (A) or the private (B); the
  dispatcher may want to decide whether row b builds its own datum or (B) is published (prove report (d)).
- O3. The prove report is 210 lines; ticket `:71` asks ≤ 150 (CLAUDE.md §6 limit 300 is met).
- O4. Report (d) item T2501a2a notes the proof also uses R1's first conjunct `g₀² ≤ lam²` (UBA-C1 table says "lam² ≤ A g₀² only"); this is in the
  merged R1 text (`TwistStep2_lam0_sq`) and in the check's UBA-C1 shape; a ticket-text note, not a statement delta.

## Verdict
- Target 2 `baIniTermGen_cltFlow` (and producers `baSTThPropsg_holds`, `baSTKpropsg_holds`, `baSTMfarg_holds`, `baSTKfargL_holds`, `baCltRepg_holds`,
  `baCltInvg_holds`): **PASS**.
- Row a2 overall: **PASS**. No dispatcher sign-off needed.
