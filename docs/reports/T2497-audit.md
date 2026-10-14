Auditor model: claude-opus-5-5
# T2497 row a (U1s2a, QGrid, targets 1-9): audit round 1

Written Wed Oct 14 01:11:51 UTC 2026 (`date -u`). Audit worktree `RBM3D-wt/T2497-audit1`, detached at `t/T2497` = `0a3b19f0`.
Row b (`t/T2497b`, targets 10-15) was not audited here.

## 1. Diff, layering, hygiene
```
$ git diff --stat main...HEAD
 RBM3D.lean                 |   2 +
 RBM3D/Chain/QGridGen.lean  | 970 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/QGridGen2.lean | 154 +++++++
$ git diff --stat main...HEAD -- RBM3D/Induction/{IterationsA,...,QProxy}.lean RBM3D/Chain/{Step34Gen,HierDriftGen,GridEnvelopeGen,ZeroModeGen,NQGood1Gen,KDecayGen}.lean RBM3D/BA | wc -l
       0
$ git diff main...HEAD -- RBM3D.lean   # +2 lines, after the last import, before #assert_rbm_axioms
+import RBM3D.Chain.QGridGen
+import RBM3D.Chain.QGridGen2
$ grep -n "^import" RBM3D/Chain/QGridGen.lean RBM3D/Chain/QGridGen2.lean
QGridGen2.lean:6:import RBM3D.Chain.QGridGen      QGridGen2.lean:7:import RBM3D.Induction.QGridB
QGridGen2.lean:8:import RBM3D.Chain.GridEnvelopeGen
QGridGen.lean:6:import RBM3D.Induction.QGridA     QGridGen.lean:7:import RBM3D.Chain.HierDriftGen
QGridGen.lean:8:import RBM3D.Chain.ZeroModeGen    QGridGen.lean:9:import RBM3D.Chain.NQGood1Gen
$ grep -rln "import RBM3D.Chain.QGridGen" RBM3D RBM3D.lean
RBM3D/Chain/QGridGen2.lean
RBM3D.lean
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^\s*axiom " RBM3D/Chain/QGridGen*.lean | wc -l
       0
```
Only the sole writable files of row a; imports are exactly the ticket's list (no `BA/*`, no other `Q*`); no band file; no frozen signature touched.

## 2. Builds and axioms (audit worktree)
```
$ lake build RBM3D.Chain.QGridGen RBM3D.Chain.QGridGen2   (error lines: grep -c error -> 0)
⚠ [3880/3881] Built RBM3D.Chain.QGridGen (10s)
⚠ [3881/3881] Built RBM3D.Chain.QGridGen2 (3.2s)
Build completed successfully (3881 jobs).
EXIT 0
$ lake build        # whole library incl. #assert_rbm_axioms (info only; the hub reruns it at merge)
Build completed successfully (4374 jobs).
full EXIT 0
$ lake env lean docs/tickets/checks/T2497-check.lean ; grep -c error
check EXIT 0
0
$ lake env lean <scratch>/pins.lean | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]"
18          # + 1 wrapped line (QGridGen2_sum_weighted_qErrQNg_instance: [propext, Classical.choice, Quot.sound])
$ ... | grep -c sorryAx
0
```
Warnings are only `longLine` style lines. `#print axioms` (19 declarations): `aTrueQNg dGridQNg aFrozQNg martIncQNg rGridQNg lkEnvNg
driftEnvNg qErrQNg QGridGen_condExp_aTrueQNg gridDriftQNg_of gridDriftQNg stoppedDuhamelQNg sum_weighted_qErrQNg_le` + the 3 bridges
+ the 3 instance theorems: all exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Statements against the pins (auditor's own uncommitted scratch file)
Scratch = the check's imports + `import RBM3D.Chain.QGridGen2` + check lines 173-293 (the binding `T2497_*` texts of the QGrid half,
verbatim) + the examples below. Result: `EXIT 0`, 0 errors.
```
142:example : @aTrueQNg = @T2497_aTrueQNg := rfl
143:example : @dGridQNg = @T2497_dGridQNg := rfl
144:example : @aFrozQNg = @T2497_aFrozQNg := rfl
145:example : @martIncQNg = @T2497_martIncQNg := rfl
146:example : @rGridQNg = @T2497_rGridQNg := rfl
147:example : @lkEnvNg = @T2497_lkEnvNg := rfl
148:example : @driftEnvNg = @T2497_driftEnvNg := rfl
149:example : @qErrQNg = @T2497_qErrQNg := rfl
151:example : T2497_SumWeightedQErrQNg := sum_weighted_qErrQNg_le
153:example : <check's "Target 6 as used" shape, verbatim> → T2497_GridDriftQNgAt Cm s t K n j σ Bk :=
       fun Cm E lam' Ψ s t K n j _m σ Bk hL hW hE hKL hKT hU hS hKK hm hl h1 h2 h3 h4 h5 h6 h7 hB =>
         gridDriftQNg s t K n j σ Bk hL hW hE hKL hKT hU hS hKK hm hl h1 h2 h3 h4 h5 h6 h7 hB
166:example : <check's "Target 7 as used" shape, verbatim> → T2497_StoppedDuhamelQNg Cm s t K n ϑ σ τ j ω :=
       fun Cm s t K n _m ϑ σ τ j ω hS h1 h2 h3 h4 h5 => stoppedDuhamelQNg Cm s t K n ϑ σ τ j ω hS h1 h2 h3 h4 h5
172:example : <check's band reading of target 1: aTrueQN / dGridQN at bandStep2Mat> := ⟨QGridGen_bandStep2_aTrueQN .., QGridGen_bandStep2_dGridQN ..⟩
177:example : <check's band reading of qErrQN at bandFM> := QGridGen_bandFM_qErrQN ..
```
- Target 1: all eight vocabulary defs are definitionally the pins (`rfl` on the `@`-constants, i.e. same binders and bodies).
- Target 6: `gridDriftQNg` has exactly the check's per-index hypotheses in the check's order and concludes the binding head
  (`m`, `C = (1+40dm)6^{dm}`, `C₂ = 1000(1+dm)²` numerals; one index `n`, no `∃` after the data). `gridDriftQNg_of` is the
  same statement for any `ϑ` with `STMollifierProps (sz.lam n) C c ϑ`, differentiability on `[0,1)` and `QGridA_Taylor2 C₂ ϑ`.
- Target 7: hypotheses `Step2Gen_USemigroup Cm.toFlowFM n`, grid facts, `j ≤ K n`; conclusion = pin.
- Target 8: the full binding Prop is closed by the theorem itself (line 151): quantifier order, four rows, `∀ᶠ n`, `∀ p ≤ K n`,
  `N^{-D_t}` identical.
- Target 5 (`QGridGen_condExp_aTrueQNg`, not pinned): band `QGridA_condExp_aTrueQN` with `hE : |E n| < 2`, `hj1 : u_{j+1} < 1`
  replaced by `LoopForm`, `WalkForm`, `KLink` at `n` and the grid facts `0 ≤ s n ≤ t n < 1`, `K n ≠ 0`, `j < K n` (these imply
  `u_{j+1} < 1`; the consumers' grid indices satisfy them). Conclusion = band's with `pathP` → `Cm.Pp`, `AvecN` → `AvecNg`.
- Targets 2-4 are private (ticket: "private"); target 2 (generator row bound from `HierDriftGen_UStep` (a)+(b), `Δ → 0⁺`) is
  proved (`QGridGen_row_thetaKer_le`, `:128`), so the narrow-gate stop rule did not fire.

Hypothesis rules over the target signatures (scratch `sig.py`: declaration text up to `:=` of the 13 public targets) and the
vocabulary bodies:
```
$ grep -cE '<C1/X1-C1 regex of the ticket>' sigs.txt
0
$ grep -nE '<same regex>' <section Vocab bodies, comments stripped>
15: STksimLKMg ... (KLloopOf d (sz.L n) σ b) +    16: STelklkMg ... (KLloopOf ...)    17: STegtMg ... (KLloopOf ...)
$ grep -cE '<X1-C4 def regex>|STGridRepNgL|∀ \(sz : Sizes d\)' RBM3D/Chain/QGridGen*.lean
QGridGen2.lean:0   QGridGen.lean:0
$ grep -cE 'sz\.withLam|\bgK\b' sigs.txt
0
```
The three vocabulary hits are the substring `Lloop` of `KLloopOf`, which the binding pin itself prescribes. No `|E|`, `etaT`,
`mE`, `mSigma`, `Ugen`, `pathP` in any generic statement; `sz.withLam` appears once, inside a proof (`QGridGen:707`).

## 4. Hidden hypotheses, vacuity, cycles
- No new `structure`/`class`; every hypothesis is a merged Prop (`StepDecompGen_LoopForm/WalkForm`, `HierDriftGen_Expand/KLoop/
  KTwo/UStep/KLink`, `Step2Gen_USemigroup`, `DecayGen_Spec`) or an inline inequality, all visible in the signature.
- No external hypothesis in row a: every class is discharged at the band carrier in the instances (§5); BA discharges are owed by
  U1-BA/U3-BA per the ticket's family table (rows 7-12), not read here.
- No cycle: the new modules import only merged upstream modules; their only importers are each other and `RBM3D.lean` (§1).
- `open private` targets `QGridA` helpers only; no `private` deleted (band files untouched).

## 5. Compiled nonempty instances (same files, built in §2)
| endpoint | instance | data | discharged |
|---|---|---|---|
| target 6 `gridDriftQNg` | `QGridGenCheck.QGridGen_gridDriftQNg_instance` (`QGridGen:924`) | `d=3`, `sz0` (`L_0=4`, `W_0=32`, `lam_0=1/64`), `Cm0 = bandStep2Mat sz0 0`, `s≡1/10`, `t≡1/2`, `K≡4`, `n=0`, `j=0<4`, `m=3`, `σ=(+,-,+,-)`, merged mollifier, `Bk` from `HierDriftGen_exists_envelope` | every hypothesis by term (`stepDecompGen_*_band`, `hierDriftGen_{expand,kLoop,kTwo,uStep,kLink}_band`, `hierDriftGen_SB_row`, `norm_mE`, `lam_pos`, `norm_num`) |
| target 7 `stoppedDuhamelQNg` | `QGridGen_stoppedDuhamelQNg_instance` (`:943`) | same, `τ≡3`, `j=4=K`, every `ω` (`min j τ = 3` Duhamel terms) | `step2Gen_USemigroup_band`, grid facts |
| target 5 | `example` (`:958`) | same, `j=0` | all |
| target 8 `sum_weighted_qErrQNg_le` | `QGridGen2Check.QGridGen2_sum_weighted_qErrQNg_instance` (`QGridGen2:133`) | `sz0`, `Cm0`, `κm = √1/2`, `s≡0`, `t≡1/2`, `K n = N_n^{31}`, `m=3`, `τ'=τK=1/2`, `D_t=1`, `C_K=31`, the target-6 constants | `DecayGen_bandSpec`, `him1`, `sz0_tendsto`, `rangeCond_half`, rows `30<31, 20<31, 10.5<31, 0.5<31` by `norm_num` |
No `N = 0`, empty index, collapsed window or `False` premise; `K n = N^{31}` is the regime the statement itself requires
(`K ≥ N^{C_K}` with `C_K` above row 1), not a size that makes the bound trivial (the 1a script shows the left side is a
nonzero sum below `N^{-1}`).

## 6. Paper deltas
Lean/paper (and Lean/band) statement differences in row a, all proposed in the prove report §(d):
- `T2497a`: per-index carrier classes in place of `|E| < 2`, `M = mI`; inline `‖m‖ ≤ 1` for `‖m‖ = 1`; row sums of `S` `≤ 1`
  for `= 1` (targets 3-7). Covers target 5's class hypotheses as well.
- `T2497b`: `DecayGen_Spec` + `∀ n, Im m ≤ 1` in place of `|E n| ≤ 2 − κ` (target 8).
No uncovered difference found.

## 7. Observations (no verdict effect)
- O1. `gridDriftQNg_of` (general `ϑ`) has no instance of its own; it is applied, with every hypothesis discharged at the merged
  mollifier, inside `gridDriftQNg`, whose instance is concrete. The pinned head of target 6 is `gridDriftQNg`'s.
- O2. Target 5 adds the grid facts `0 ≤ s n ≤ t n < 1`, `K n ≠ 0`, `j < K n` in place of the band's `u_{j+1} < 1`; the same grid
  facts are hypotheses of target 6, so its consumers already hold them.
- O3. Prove report §(b) says integrability uses `HierDriftGen_integrable_LIM`, not `norm_loopFine_crudeNg` (ticket target 3
  wording); the private route differs, no statement changes.
- O4. Extra public names (3 bridges, `QGridGen_sigma4(_alternating)`, `QGridGen2_Kc31`) are stem-prefixed (rule (E)).

## Verdict
| target | verdict |
|---|---|
| 1 vocabulary (8 defs) | PASS |
| 2-4 (private kernel step, algebra, drift envelope) | PASS |
| 5 `QGridGen_condExp_aTrueQNg` | PASS |
| 6 `gridDriftQNg_of`, `gridDriftQNg` | PASS |
| 7 `stoppedDuhamelQNg` | PASS |
| 8 `sum_weighted_qErrQNg_le` | PASS |
| 9 instances | PASS |
Overall row a (T2497, `t/T2497`): **PASS**. No dispatcher sign-off needed.
