Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct 11 10:50:37 UTC 2026

### (i) Exponent table

Targets: (1) `BAFAav d → GreenLocal_FAav d`; (2) `baGbEXPav_holds d (hd : 2 ≤ d) : BAGbEXPav d`; (3) registry edits. No new analytic exponent is introduced: the only
quantities are those already in the two merged pins, which are composed, not re-estimated.

| quantity | value | constraint | slack |
|---|---|---|---|
| dimension guard | `2 ≤ d` (that of `baGbEXPii_holds` `GreenLocal.lean:474`, `greenLocal_gbEXPav_of_fa` `:793`) | needed by GL2 inside the wiring; `BAFAav` itself holds for every `d` (`GreenCond2.lean:1730`) | at `d = 3`: 1 |
| entrywise exponent inside the wiring | `ε₀/2` | `0 < ε₀/2` for `ε₀ > 0` (supplied by `baGbEXPii_holds … (ε₀/2) (half_pos hε₀)`, `GreenLocal.lean:795-797`) | `ε₀/2 > 0`, no upper constraint |
| window of `Ψ` | `W^{-d/2} ≤ Ψ ≤ W^{-ε₀}` (identical in `BAGavLGEX`, `BAFAav`, `GreenLocal_FAav`) | nonempty iff `ε₀ ≤ d/2` | `d = 3, ε₀ = 1/10`: exponent gap `7/5` |
| `τ` of `BAFamGain`/`BAFAav` proof (internal to `baFAav_holds`) | `0 < τ ≤ ε₀/2` | not a hypothesis of the targets | `ε₀ = 1/10, τ = 1/20`: 0 (equality allowed) |
| premise `STInitialGT2gL … ε₀ Ψ` | kept inside the `Prop` (binder of `BAGavLGEX`, `BAFAav`) | no new hypothesis (C1) | n/a |

Target 1 comparison (script, `GreenMinor3.lean:858-869` def body of `BAFAav` against `GreenLocal.lean:744-755` def body of `GreenLocal_FAav`, names normalised by `sed`):
result `IDENTICAL` (12 lines each), so `BAFAav d → GreenLocal_FAav d` is `id` / `Iff.rfl`; no congruence needed, no difference in substance.

### (ii) Concrete nondegenerate instance and the three questions

Instance: `d = 3`, `ε₀ = 1/10` (so `ε₀/2 = 1/20`), window nonempty, `W = 100`, `Ψ = W^{-1/2}`; target 4 is `BAGbEXPav 3` from `baGbEXPav_holds 3 (by norm_num)`, guard `2 ≤ 3`.

```
$ python3 -I inst.py
guard 2<=d: True  slack 1
eps0/2 = 1/20 >0: True
window exponent lo=-3/2 <= hi=-1/10: True, gap=7/5
tau=1/20 <= eps0/2=1/20: True slack 0
W=100, Psi=W^-1/2=0.1000; W^-d/2=1.00e-03 <= Psi <= W^-eps0=0.6310: True
$ diff <(def body BAFAav, name→NAME) <(def body GreenLocal_FAav, name→NAME)
diff: IDENTICAL (12 lines, def bodies, names normalised)
```

No external hypothesis: `BAFAav` is proved (`baFAav_holds`), the wiring is proved (`greenLocal_gbEXPav_of_fa`), so no concrete-limit computation is owed.
`STInitialGT2gL` remains a premise inside the `Prop` as in the band pin; it is not a hypothesis of any target.

(ii-a) Consumers on `main` (command `grep -rn --include='*.lean' "BAGbEXPii\|BAGbEXPav\|baGbEXPii_holds\|baGbEXPav" RBM3D RBM3D.lean`):
- `BAGbEXPav`: no consumer outside its definition `Step1Boot.lean:123`, `GreenLocal.lean:788/862` (the wiring and its example) and the registry line `Test/Axioms.lean:195`.
- `BAGbEXPii`: hypotheses (not applications of the proof) in `Step1.lean:576, 686, 703, 715, 726, 736, 748, 764`, `Step1Fam.lean:695, 983, 1001, 1018`,
  `Step1Boot.lean:261, 712`, `GreenMinor3.lean:915`; the proof `baGbEXPii_holds` is used only in `GreenLocal.lean` (`:759` bridge, `:795` wiring).
  The consumers are stated for `d` generic or `d = 3`; the guard `2 ≤ d` is met for `d = 3` (slack 1), so moving a consumer to the proved pin is possible but not part of this ticket (G7).
  Removing `BAGbEXPii` from `owedProps` changes no hypothesis: the registry's check is that a premise found in theorem types is classified or proved (`Test/Axioms.lean:514-520`; `BAGbEXPii` is then proved by `baGbEXPii_holds`).

(ii-b) The three registry edits (`Test/Axioms.lean`, `owedProps`; current lines): delete line 193 (`RBM.BA.BAGbEXPii`) and line 195 (`RBM.BA.BAGbEXPav`);
keep line 194 (`RBM.BA.BAGbEXPij`, G7); in line 196 (`RBM.BA.STInitialGT2gL`) replace the owner text "owner BA-G6b (the BA Step 1 / `(initialGT2)` chain)" by
"owner BA-V (the BA Step 1 / main-induction chain), as the band's `STInitialGT2` (`Test/Axioms.lean:129`)". `RBM3D.lean`: last import is `import RBM3D.Chain.Step2Kern` (line 458),
`#assert_rbm_axioms` at line 461; add `import RBM3D.BA.GbEXPav` after the last `import` line. The new file must import `RBM3D.BA.GreenLocal` (for `greenLocal_gbEXPav_of_fa`, `GreenLocal_FAav`)
and `RBM3D.BA.GreenCond2` (for `baFAav_holds`; `BAFAav` is defined in `GreenMinor3`, which `GreenCond2` reaches via `GreenCond`, `GreenCond.lean:6`).

### Verdicts

- Target 1 `baFAav_greenLocal`: PASS (`Iff.rfl`/`id`; statements textually identical).
- Target 2 `baGbEXPav_holds`: PASS (`fun` composition `greenLocal_gbEXPav_of_fa d hd (baFAav_greenLocal d (baFAav_holds d))`; guard `2 ≤ d`).
- Target 3 registry: PASS (three edits as listed; no consumer of `BAGbEXPav`; consumers of `BAGbEXPii` unaffected).
- Target 4 instance: PASS (`d = 3`, guard slack 1, window gap 7/5).


## (b) Script output — Sun Oct 11 10:53 UTC 2026 (commit c2be2dd on t/T2422)

```
$ lake build RBM3D.BA.GbEXPav | tail -1 ; lake build | tail -1   # full build runs #assert_rbm_axioms
Build completed successfully (3804 jobs).
Build completed successfully (4230 jobs).
$ lake env lean docs/tickets/checks/T2422-check.lean ; echo exit $?
exit 0
'RBM.BA.baGbEXPav_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baFAav_greenLocal' depends on axioms: [propext, Classical.choice, Quot.sound]
$ wc -l RBM3D/BA/GbEXPav.lean; git diff --numstat RBM3D/Test/Axioms.lean   # stop line 400
30 RBM3D/BA/GbEXPav.lean
1	3	RBM3D/Test/Axioms.lean
$ git diff --stat main...t/T2422 | tail -4
 RBM3D.lean             |  1 +
 RBM3D/BA/GbEXPav.lean  | 30 ++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |  4 +---
$ grep -rn --include='*.lean' "baFAav_greenLocal\|baGbEXPav_holds" RBM3D | grep -v BA/GbEXPav.lean
(no output: no name clash)
$ sed -n 21,30p RBM3D/BA/GbEXPav.lean
theorem baFAav_greenLocal (d : ℕ) : BAFAav d → GreenLocal_FAav d := fun h => h

/-- **`lem_GbEXP_BA`, `(GavLGEX)`** at block Anderson (`7_8:1916-1946`), the pin `BAGbEXPav`. -/
theorem baGbEXPav_holds (d : ℕ) (hd : 2 ≤ d) : BAGbEXPav d :=
  greenLocal_gbEXPav_of_fa d hd (baFAav_greenLocal d (baFAav_holds d))

/-- Compiled nonempty instance: `d = 3`. -/
example : BAGbEXPav 3 := baGbEXPav_holds 3 (by norm_num)

end RBM.BA
```

Registry: removed `BAGbEXPii`, `BAGbEXPav` from `owedProps`; `BAGbEXPij` kept (G7); owner of `STInitialGT2gL` now "BA-V (the BA Step 1 /
main-induction chain), as the band's `STInitialGT2` (`Test/Axioms.lean:129`)". Import line added to `RBM3D.lean` after `RBM3D.Chain.Step2Kern`.
Target 1 is the identity (statements identical, section (a)); target 2 composes `greenLocal_gbEXPav_of_fa d hd` with `baFAav_holds d`; no new hypothesis.
No port from RBM1D/RBM2D.

## (c) Mathlib names
None used beyond the `norm_num` tactic.

## (d) Open issues
Guard `2 ≤ d` as T2408b, T2403a; no new paper-delta. G7 moves the `BAGbEXPii`/`BAGbEXPij` consumers.
