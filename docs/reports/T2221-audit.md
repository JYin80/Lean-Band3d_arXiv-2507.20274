Auditor model: claude-opus-5-5

# T2221 (S5-11a, `Induction/PfStep5Grid`) — audit round 1 — Mon Oct  5 23:33:22 UTC 2026

Branch `t/T2221` at 2232c1c; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2221-audit1` (detached); `$S` = scratch dir.

## 1. Files touched

```
$ git diff --name-only main...t/T2221
RBM3D/Induction/PfStep5Grid.lean
$ git merge-base main t/T2221; git diff --name-only <base> main -- RBM3D
e9ef940
RBM3D/Induction/ExpDuhamel.lean  RBM3D/Induction/ExpEtermsA.lean  RBM3D/Induction/ExpIniI.lean
RBM3D/Main/FixedZ.lean  RBM3D/Test/Axioms.lean        (new files / registry only; no import of this module changed)
```
Only the sole writable file (1292 lines); `Test/Axioms.lean` untouched (no registry line expected). Imports exactly `PfStep5Alg`, `Step2Iterate`, `GridDuhamelN`.

## 2. Statements: vocabulary + five pins vs the check file (script diff)

Extraction: from `noncomputable def PfStep5Grid_level` to the last line of `PfStep5Grid_duhamel_pin`,
docstrings and blank lines removed, applied to `docs/tickets/checks/T2221-check.lean` and to the Lean file.
```
$ ext $C > $S/check.txt; ext $F > $S/file.txt; wc -l ...; diff $S/check.txt $S/file.txt && echo "DIFF EMPTY ..."
      44 .../check.txt
      44 .../file.txt
DIFF EMPTY (vocabulary + 5 pins)
```
Target signatures (each ascribes the pin, so its statement is the pin body by definition):
```
$ grep -n "^theorem pfStep5Grid_\(level\|Jsharp\|stop\|below\|duhamel\) " $F
149:theorem pfStep5Grid_level : PfStep5Grid_level_pin := by
191:theorem pfStep5Grid_Jsharp {d : ℕ} (sz : Sizes d) : PfStep5Grid_Jsharp_pin sz := by
213:theorem pfStep5Grid_stop {d : ℕ} (sz : Sizes d) : PfStep5Grid_stop_pin sz := by
222:theorem pfStep5Grid_below {d : ℕ} (sz : Sizes d) : PfStep5Grid_below_pin sz := by
892:theorem pfStep5Grid_duhamel (d : ℕ) : PfStep5Grid_duhamel_pin d := by
```
Binder lines match the ticket's "Targets" list token for token.

Against the ticket's mathematics: target 1 has `1 < W`, `u ≤ u' < 1`, the four conjuncts of DECISIONS §70 (1)
(exact identity `W^{-D_{u'}} = (1-u')^{-2}W^{-D*}`, monotonicity, `≤ D*` for `u ≥ 0`, `≥ D*-2d` under
`W^{-d} ≤ 1-u'`). Target 4: `∀ L [NeZero L], 3 ≤ L`, all of `g E Δ M R σ k u A F Rem Mart` universally
quantified, hypotheses `|E| ≤ 2`, `0 ≤ Δ`, `0 ≤ u 0`, equal steps, `u k < 1`, sup bounds `M`, `R` for `j ≤ k`,
the additive decomposition for `j ≤ k`; conclusion with loss `64 (1-u_k)^{-7}(R + ΔM)` and the martingale
weighted by `Ugen (u j) (u k)`, as in the ticket (step 5 total `≤ 64B⁷(R+ΔM)`). No `kΔ < 1` premise is needed
(it follows from `0 ≤ u 0`, `u k < 1`). Targets 3a/3b: `∀ s t K E Dst ε n (j ω)`, no extra premise.
Fixed-parameter order: all deterministic, `∀ n`, no `∀ᶠ` (§29 checklist (4)). No special case of a more
general pin: these are the general pinned statements.

## 3. Hidden hypotheses, vacuity, cycles

- All five pins are `def … : Prop` with every hypothesis in the binder list; the three vocabulary objects are
  `noncomputable def`s of type `ℝ` / `PathΩ sz → ℕ`; no structure fields, no `Prop`-valued class.
- No external hypothesis is introduced (nothing assumed; no registry line).
- Dependencies: merged names only (`STLKM_measurable`, `isStoppingTime_firstHit_grid`, `lt_firstHit_imp`,
  `LemDecCalELip_Jsharp`, `STLM_seqHflow`, `Ugen`/`UN`/`ThetaN` kernel facts); module builds against main's
  upstream (§1); no pin of this ticket is used to prove another (targets 1-3b are independent of 4).
- Observation (not a delta of this ticket): `PfStep5Grid_JsharpM = max 1 (sup …)`; the paper's
  `(eq:def_TTT)` has no `max 1`. For `W > 1`, `ε > 0` the stopping condition `max(1,x) ≥ W^ε ⇔ x ≥ W^ε`
  is the same; for `ε ≤ 0` the index is `0`. The `max 1` is inherited from the merged `LemDecCalELip_Jsharp`
  and is already numbered as D499 (T2198c) in `docs/paper-deltas.md:1458`.

## 4. Compiled nonempty instances (in the same file)

| target | instance | data | hypotheses |
|---|---|---|---|
| 1 | `pfStep5Grid_inst_level` (:1137) | `d=3, W=32, D*=55, u=0, u'=1/16` | all discharged (`norm_num`); conjunct 4 premise `32^{-3} ≤ 15/16` proved |
| 2 | `pfStep5Grid_inst_Jsharp` (:1150) | `sz0, n=0, u=1/16, E=STflowE z0, D=55, ω≡0` | none (equation) |
| 3a | `pfStep5Grid_inst_stop` (:1157) | `sz0, s≡0, t≡1/16, K≡8, E=STflowE z0, D*=55, ε=1/50, n=0`; also proves `gridStep = 1/128` | none |
| 3b | `pfStep5Grid_inst_below` (:1210) | `sz0, s≡0, t≡1/16, K≡8, E≡0, D*=55, ε=1/50, j=0, ω≡0` | `0 < T(ω)` **discharged** (`J♯ = 1 < 32^{1/50}` at `H = 0`) |
| 3b | `pfStep5Grid_inst_below_flow` (:1169) | ticket data at `E = STflowE z0` | `0 < T(ω)` kept, as the ticket allows |
| 4 | `pfStep5Grid_inst_duhamel` (:1184) | `d=3, L=4, g=1/64, E=0, σ=![true,false], u j=j/48, k=3, Δ=1/48, A≡0, F≡0, Rem j=j/10, Mart j=-j/10, M=0, R=3/10` | all discharged (`|E|≤2`, `Δ≥0`, `u0≥0`, steps, `3/48<1`, bounds, decomposition) |

Instance of target 4 is exactly the ticket's prescribed data (`k = 3`, nonzero `Rem`, `Mart`, window
`[0, 1/16]`). Observation: `A ≡ 0`, `F ≡ 0`, `M = 0` make the drift part trivial at this instance; the ticket
prescribes this data, and the file also applies target 4 at the generic consumer data (unnamed `example`,
:1243, `STgAN`/`STgDriftN` at `m = 2`, `UN … (fun i' => mSigma E (σ i'))` for the martingale sum, closed by
`rfl` after `Finset.Icc_eq_empty_of_lt (2 < 3)`), which confirms the consumer fit of §45 O2. No `N = 0`,
empty index, collapsed window, `False` premise or huge witness.

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.PfStep5Grid > $S/build.log 2>&1; echo "exit $?"
$ grep -c "^error" $S/build.log; tail -3 $S/build.log
0
✔ [3847/3847] Built RBM3D.Induction.PfStep5Grid (17s)
Build completed successfully (3847 jobs).
exit 0
```
(140 warning lines, all in upstream modules: long lines, docstring placement; none in `PfStep5Grid.lean`.)
```
$ grep -nE "\bsorry\b|\badmit\b|^axiom|^\s*axiom |native_decide" RBM3D/Induction/PfStep5Grid.lean; echo $?
1
$ lake env lean $S/Ax.lean    # #print axioms of the 5 targets and 6 named instances
'RBM.Gauss.Sizes.pfStep5Grid_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_Jsharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_stop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_inst_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_inst_Jsharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_inst_stop' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_inst_below_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_inst_below' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.pfStep5Grid_inst_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ printf 'import RBM3D\nimport RBM3D.Induction.PfStep5Grid\n#assert_rbm_axioms\n' > $S/Reg.lean
$ lake env lean $S/Reg.lean > $S/reg.log 2>&1; echo "exit $?"; head -4 $S/reg.log
exit 0
axiom audit: 6606 theorems, 2249 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
```
Frozen signatures: no merged file is touched (§1).

## 6. Public names and helper hygiene

```
$ for n in <14 public names/prefixes>; do git grep -c "$n" main -- RBM3D | wc -l; done   # all 0
PfStep5Grid_level 0  PfStep5Grid_JsharpM 0  PfStep5Grid_stopIdx 0  PfStep5Grid_{level,Jsharp,stop,below,duhamel}_pin 0
pfStep5Grid_{level,Jsharp,stop,below,duhamel} 0  pfStep5Grid_inst_ 0
$ grep -nE "^(theorem|lemma|def|noncomputable def|abbrev|structure|instance)" $F   # non-private
71/76/85 the three vocabulary defs; 97-130 the five pins; 149/191/213/222/892 the five targets;
1137/1150/1157/1169/1184/1210 pfStep5Grid_inst_{level,Jsharp,stop,below_flow,duhamel,below}
```
Every other declaration is `private` with prefix `pfStep5Grid_` (§3 (E)); public names exactly as pinned.

## 7. Paper-delta coverage

| Lean/paper difference | coverage |
|---|---|
| `(eq:def_TTT)` as a grid stopping index at the time-dependent level `D_{u_j}` (vocabulary, targets 1, 3a, 3b) | prove report (d) **T2221a** |
| `(int_K-L_ST)` derived from the additive grid decomposition with explicit remainder `64(1-u_k)^{-7}(R+ΔM)`, martingale weighted by `𝒰_{u_j,u_k}` (target 4) | prove report (d) **T2221b** |
| `J♯ = max(1, …)` realized control (vocabulary, target 2) | already numbered D499 (T2198c), `docs/paper-deltas.md:1458` |

No uncovered difference found.

## 8. Verdicts

- Target 1 `pfStep5Grid_level`: **PASS**
- Target 2 `pfStep5Grid_Jsharp`: **PASS**
- Target 3a `pfStep5Grid_stop`: **PASS**
- Target 3b `pfStep5Grid_below`: **PASS**
- Target 4 `pfStep5Grid_duhamel`: **PASS**

Ticket T2221: **PASS**. No dispatcher sign-off needed. Observations (no RETURN): `max 1` in `J♯` (covered by
D499); the target-4 instance has `A ≡ 0`, `F ≡ 0`, `M = 0` as the ticket prescribes, supplemented by the
generic consumer-check `example`.
