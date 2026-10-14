Auditor model: claude-opus-5-5
# T2508b audit (row b: targets 9-12), round 2 — Wed Oct 14 17:18:29 UTC 2026
Branch `t/T2508b` at c490c2e3 (repair of round 1; base 57178a34); audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2508b-audit2` (detached, clean).
Scratch (uncommitted, outside the repo): `<scratchpad>/T2508b/audit2/{pin.lean,deg2.lean,*.log,*.out}`.

## Verdicts
| target | statement | hidden hyp / cycle | instance | build / axioms | verdict |
|---|---|---|---|---|---|
| 9 `QopDecayGen_ThetaN_fastDecayg` (+ `ThetaN2`, band `STthetaOp` re-derivation) | = `T2508_QopDecayGenOf` (both directions) | none | ok at `sz0`; window nonempty, proved in each example | ok | PASS |
| 10 `expIntIQ_src_sumZerog`, `expIntIQ_f_leg`, `expIntIQ_D_leg` | not pinned; ticket math | none | ok | ok | PASS |
| 10 `expIntIQ_src_decayg` | not pinned; ticket math | none | ok at `(sz0, z0)`; window nonempty, proved in the example | ok | PASS |
| 11 `expIntIQ_inig`, `_star_boundg`, `_backg`, `_conclg` | conclusion `STExpIntQConclgL'` = binding `T2508_ExpIntQConclgL'` (rfl) | none | ok (other gates' pins as hyps) | ok | PASS |
| 12 `stExpIntIgL'_of` (+ 3 band re-derivations) | proves `T2508_RowBOf`; `STExpIntIgL'` = `T2508_ExpIntIgL'` (rfl) | none | ok (every family premise discharged at the band tuple) | ok | PASS |
Ticket verdict: **PASS**. No dispatcher sign-off needed.

## 0. The repair only changes instances
```
$ git diff --stat b173ce5f c490c2e3
 RBM3D/Chain/ExpIntIQGen.lean |  56 ++++++++----
 RBM3D/Chain/QopDecayGen.lean | 198 ++++++++++++++++++++++++++++++++-----------
$ grep -n "^section Instances" QopDecayGen.lean ExpIntIQGen.lean  →  QopDecayGen.lean:266, ExpIntIQGen.lean:1227 (headers :260, :1220)
$ git diff -U0 b173ce5f HEAD | grep "^@@"      (new-side starts)
ExpIntIQGen: +58,2 (an `open private … from RBM3D.Chain.QopDecayGen` line), +1259,27, +1288,11
QopDecayGen: +260,5 +268,51 +320,18 +339,17 +357,4 +362,8 +371,2 +375 +377 +380,2 +390,9 +400 +402,5 +409,7 +417 +419,14 +434,4
```
All hunks lie in the instance sections, except one `open private` line. No target statement, hypothesis, registry line or import line changed since round 1, so §1, §2 and §5 of round 1 stand. They are re-run below on c490c2e3.

## 1. Statements against the pins
```
$ cmp <(pin.lean minus `import RBM3D.Chain.ExpIntIQGen`, first 248 lines) docs/tickets/checks/T2508-check.lean
pin.lean = T2508-check.lean (verbatim, 248 lines) + import ExpIntIQGen + audit examples
$ lake env lean pin.lean ; echo exit=$?      → exit=0, 0 errors
example (d n : ℕ) : T2508_QopDecayGenOf d n := QopDecayGen_ThetaN_fastDecayg d n
example (d : ℕ) : T2508_QopDecayGenOf d 2 := QopDecayGen_ThetaN2_fastDecayg d
example … (h : T2508_QopDecayGenOf d n) : <QopDecayGen_ThetaN_fastDecayg's own type, copied> := h hd Λ K C₀ ε D C₆ hΛ hε hC₆
example … : T2508_RowBOf d law Flow mk T0 Ker gK Aof := fun hB hK hT hB45 hSR hSR2 hDuQ =>
    stExpIntIgL'_of gK hB.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2 hSR hSR2 hK.1 hK.2 hT hB45 hDuQ
example … : T2508_ExpIntIgL' d law Flow mk T0 = STExpIntIgL' d law Flow mk T0 := rfl
$ lake env lean docs/tickets/checks/T2508-check.lean ; echo check_exit=$?   → check_exit=0, 0 errors
```
- Target 9 equals the pin up to currying. `∃ W₀` comes after `(Λ,K,C₀,ε,D,C₆)`, and `C₆` comes before `(sz,C,gK)`. The only link from `gK` to `lam` is `gK k ≤ sz.lam k` (W-q, UBA-C1).
- Target 12: every premise of `T2508_RowBOf` is fed to `stExpIntIgL'_of`. The `Step2EventsGen_Flow` conjunct of `T2508_FamBase` is not used, so the hypotheses are weaker (allowed).
- Targets 10-11 are not pinned (the ticket only maps band → generic). Their hypotheses are the ticket's family rows: 17, 9′, 19′, 22 and 16. They also take other gates' conclusions: `STExpDriftHiConclgL`, `STExpDriftDecayConclgL`, `STExpWardIConclgL'`. None of them reads `STImproveExpAvergL` or `st6_expAvgU_of_ping` (V1L-C1).

## 2. Hidden hypotheses, vacuity, cycles
```
$ grep -nE '^(noncomputable )?(private )?(def|abbrev|structure|class|instance) ' QopDecayGen.lean ExpIntIQGen.lean   → (no output)
$ grep -nwE 'sorry|admit|axiom|native_decide' <both>      → (no output)
$ grep -nE 'import RBM3D\.(BA|Chain\.Step2Kern)' <both>   → (no output)
```
There is no new structure, so no hypothesis sits in a structure field. Every dependency is a merged module, and no merged file imports the new files, so there is no cycle.

## 3. Compiled nonempty instances (round-1 defect: fixed)
Data: `sz0` (`Defs/Sizes:260`: `L_k = 4(k+1)`, `W_k = (2(k+1))^5`, `lam_k = (2(k+1))^{-6}`) and `EKFastDecay` (`Evolution/Pins:51`: far window `W^ε ℓ ≤ zdistD(a_i − a_j)` ⇒ `‖A a‖ ≤ W^{-D}`).
- **Target 9** (`QopDecayGen.lean:392`, `:409` `n = 2` form, `:426` band `STthetaOp`). Inputs: `bandFM sz0 0`, `gK = lam`, `Λ = 1`, `K = 3`, `C₀ = 1`, input `(ε, D) = (1/10, 5)`, `u = 1/2`, `k = ⌈W₀⌉₊`, and the delta tensor `𝟙_{a=0}`. The class `Step5KerGen_ThDecay` is discharged by the merged `step5KerGen_thDecay_band`. No hypothesis remains. Each example also proves `¬ ∀ A, EKFastDecay … (1/10) 5 A` (input) and `¬ ∀ A, EKFastDecay … (2·(1/10)) (5−(3+1)) A` (output) at the chosen `k`. So the round-1 test `aud_D1` now fails at this data, and the conclusion is a real constraint on `Θ^{(2)}𝟙_0`.
- **`expIntIQ_src_decayg`** (`ExpIntIQGen.lean:1279`). Flow `(sz0, z0)` (`flow_z0`), window `[0, 1/16]`, `ε' = 1/5`, `D = 1`. Row 22 is discharged by `step5KerGen_thDecay_band` and row 19′ by `b45Gen_facts_band`. The envelopes come from the private `ExpIntIQGen_sz0Env`, via `iniTermGen_cltFlow_band` and `sixteenth_le_lemT`, with no hypothesis. The hypotheses that remain are `hdr : STExpDriftHiConclgL` and `hdd : STExpDriftDecayConclgL` at this flow: these are T2506 conclusions, i.e. other gates' outputs. The second conjunct proves the window is nonempty for every `n` and every `v ∈ [0,1/16]`, so the round-1 test `aud_D3` fails here.
- Independent re-use of the helpers (audit file, `open private`):
```
$ lake env lean deg2.lean ; echo exit=$?   → exit=0
QopDecayGen_sz0_nontriv : ∀ (k : ℕ) {ε g t D : ℝ},
  ε ≤ 1 / 5 → 0 < D → ellT (sz0.L k) g t ≤ 1 → ¬∀ (A : (Fin 2 → Zd 3 (sz0.L k)) → ℂ), EKFastDecay g t (↑(sz0.W k)) ε D A
QopDecayGen_sz0_far : ∀ (k : ℕ) {ε g t : ℝ},
  ε ≤ 1 / 5 → ellT (sz0.L k) g t ≤ 1 → ∃ a i j, ↑(sz0.W k) ^ ε * ellT (sz0.L k) g t ≤ ↑(zdistD 3 (sz0.L k) (a i - a j))
'_private.RBM3D.Chain.QopDecayGen.0.RBM.BA.QopDecayGen_sz0_nontriv' depends on axioms: [propext, Classical.choice, Quot.sound]
theorem aud2_not_D1 (k : ℕ) (v : ℝ) (hv : v ≤ 3 / 4) :   -- every k, every v ≤ 3/4: input and output windows nonempty
    (¬ ∀ A, EKFastDecay (sz0.lam k) v (sz0.W k) (2 * (1 / 10)) (5 - (3 + 1)) A) ∧ (¬ ∀ A, EKFastDecay (sz0.lam k) v (sz0.W k) (1 / 10) 5 A)
'aud2_not_D1' depends on axioms: [propext, Classical.choice, Quot.sound]
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.L 9 = 40 ∧ sz0.W 9 = 3200000 := by decide   -- compiles
```
- Unchanged since round 1 and still fine: `:1243`, `:1248`, `:1253`, `:1311`, `:1331`, `:1360`, `:1375`, `:1397`, `:1401`, `:1407`. Target 12 (`:1397`, via `ExpIntIQGen_stExpIntIgL'_band`) is applied at the band tuple, with every family premise discharged by merged band theorems.

## 4. Build and axioms
```
$ lake build RBM3D.Chain.QopDecayGen RBM3D.Chain.ExpIntIQGen ; echo exit=$?
⚠ [3958/3959] Built RBM3D.Chain.QopDecayGen (13s)
⚠ [3959/3959] Built RBM3D.Chain.ExpIntIQGen (12s)
Build completed successfully (3959 jobs).
exit=0
$ (warnings in the two modules other than the 100-character longLine lint) → (none)
$ #print axioms (pin.lean): 15 declarations, each "depends on axioms: [propext, Classical.choice, Quot.sound]"
  QopDecayGen_ThetaN_fastDecayg, QopDecayGen_ThetaN2_fastDecayg, QopDecayGen_STthetaOp_fastDecay_band, expIntIQ_src_sumZerog,
  expIntIQ_f_leg, expIntIQ_D_leg, expIntIQ_src_decayg, expIntIQ_inig, expIntIQ_star_boundg, expIntIQ_backg, expIntIQ_conclg,
  stExpIntIgL'_of, ExpIntIQGen_stExpIntIgL'_band, ExpIntIQGen_stExpIntI'_band, ExpIntIQGen_stStep6I_of_LW_band
$ git diff --stat main...t/T2508b
 RBM3D.lean                   |    2 +
 RBM3D/Chain/ExpIntIQGen.lean | 1414 +++++
 RBM3D/Chain/QopDecayGen.lean |  443 +++
 RBM3D/Test/Axioms.lean       |    3 +-
$ git diff main...HEAD --name-only -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Chain/{ExpIntIGen,ExpWardIIGen,ExpIntEasyGen}.lean | wc -l
0
$ git diff main...HEAD -- RBM3D.lean RBM3D/Test/Axioms.lean | grep "^[+-][^+-]"   (abridged)
+import RBM3D.Chain.QopDecayGen
+import RBM3D.Chain.ExpIntIQGen
- `RBM.BA.STExpIntIgL, … generic: V1s2'/V1s3'; BA: V1-BA
- `RBM.BA.STExpIntIgL', … generic: proved by `stExpIntIgL'_of` (T2508 row b, `Chain/ExpIntIQGen`) …   (row a's owedProps line removed)
+ `RBM.BA.STExpIntIgL, … superseded by `STExpIntIgL'` (T2508 row b, `stExpIntIgL'_of`, `Chain/ExpIntIQGen`); unprimed: no producer …
```
The diff touches only the sole writable files. No band or merged file is touched, and no frozen name changes. The files are 443 and 1,414 lines (1,857 in total), under the 2,000-line file stop and the 2,350-line row stop. The registry edit matches the ticket's row-b instruction. The full build is the hub's job.

## 5. Paper deltas
The only Lean/paper statement difference in row b is D725, already merged in `docs/paper-deltas.md:1808`; row a's use of it is D732 (`:1833`). The generic Duhamel text is eventual, so `STExpIntI'_of_gL'` holds in one direction only; `ExpIntIQGen_stExpIntI'_band` uses it. Target 9 keeps the band exponents `(2ε, D−(K+1))`. The repair changed instances only, so there is no new delta. Coverage is complete, and the prove report's (d) ("candidates: none") is consistent with this.

## Observations (no RETURN)
- O1. The instances of targets 10 (envelopes, sum-zero) and 11 at `szB` (`L = 4`) do not exercise the fast-decay inputs, because their decay windows are empty. Their conclusions are `PrecL` bounds or algebraic identities, and are not shown to be trivial. Carried over from round 1.
- O2. The ticket names the envelopes `expIntIQ_f_le` and `_D_le`. They are public as `expIntIQ_f_leg` and `expIntIQ_D_leg`, without the file stem. The name-clash grep was clean in round 1.
- O3. For the hub: `git merge-tree --write-tree main t/T2508b` reports textual conflicts in `RBM3D.lean` and `RBM3D/Test/Axioms.lean` against the current `main`, which now includes T2509 and T2510. The ticket and CONTROL H310 (3) say these two files are a union of lines at merge.
