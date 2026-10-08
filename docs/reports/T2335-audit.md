Auditor model: claude-opus-5-5

# T2335 audit (round 1) — BA-P4b `RBM3D/BA/KHeatTail.lean`, target `kBA_le`

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2335-audit1`, detached at `t/T2335` = `6c88c68`; merge base = `main` = `5b6221f`.
Written Thu Oct  8 13:28:44 UTC 2026 (`date -u`). Scratch: `<scratchpad>/T2335/audit/`.

## 1. Statement against the pin (check file section 2)
```
$ sed -n '/^def T2335_kBA_le : Prop :=/,/zdistD d L a : ℝ))$/p' docs/tickets/checks/T2335-check.lean | sed 1d | tr -s ' \n' ' ' > pin.txt
$ sed -n '/^theorem kBA_le :/,/:= by$/p' RBM3D/BA/KHeatTail.lean | sed 's/^theorem kBA_le ://; s/ := by$//' | tr -s ' \n' ' ' > lean.txt
$ diff pin.txt lean.txt && echo "pin == Lean statement (whitespace-normalised)"
pin == Lean statement (whitespace-normalised)
```
Check-file equality (check file + `import RBM3D.BA.KHeatTail` + `example : RBM.BA.T2335Check.T2335_kBA_le := RBM.BA.kBA_le`):
```
$ diff docs/tickets/checks/T2335-check.lean checkeq.lean
9a10
> import RBM3D.BA.KHeatTail
48a50,51
> example : RBM.BA.T2335Check.T2335_kBA_le := RBM.BA.kBA_le
>
$ lake env lean checkeq.lean 2>&1 | grep error ; echo "checkeq exit ${pipestatus[1]}"
checkeq exit 0
```
Statement content (read off the signature): `∀ d, 2 ≤ d → ∀ Λ κ > 0, ∃ C c > 0, ∀ L [NeZero L], 3 ≤ L → ∀ g E m, 0 < g → g ≤ Λ → BAReal d L g κ E m →
∀ τ, 0 < τ → τ ≤ L² → ∀ a, kBA d L g E m τ a ≤ C·min 1 (τ^{-d/2})·exp(-c·min(zdistD²/τ, zdistD))`.
Constants are chosen after `(d, Λ, κ)` and before `L, g, E, m, τ, a`: uniform in `L, g, E, m`, as the ticket requires. Full regime (i)
`0 < τ ≤ L²`, all `a`, no floor `L^{-d}`, full exponent `-d/2`, the Gaussian/exponential `min`. It is the twin of `Heat.kProd_le`
(`HeatProduct.lean:439`) with `kProd d L τ ↦ kBA d L g E m τ` plus the kernel hypotheses `2 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`, `BAReal`, all
part of the pin. Not a special case or a conditional adapter.

The object `kBA` (merged, `KHeat.lean:50-55`): `BAP … s a b = exp(-s) Σ' n, sⁿ/n! (BAK^n) a b`, `kBA … τ a = BAP … (τ/g²) 0 a`. This is the
ticket's `P_{τ/g²}(0,·)`.

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -n -E "^(private )?(theorem|lemma|def|abbrev|structure|class|instance|axiom|opaque)" RBM3D/BA/KHeatTail.lean | grep -v private
515:theorem BAP_tail_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ cT : ℝ, 0 < cT ∧
631:theorem kBA_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
758:theorem inst_zdistD : zdistD 3 4 (![1, 0, 2] : Zd 3 4) = 3 := by
762:theorem inst_kBA_le :
775:theorem inst_tail_le :
$ grep -n -E "sorry|admit|native_decide|^axiom|set_option|implemented_by|extern" RBM3D/BA/KHeatTail.lean
29:set_option linter.style.longLine false
30:set_option linter.unusedSimpArgs false
31:set_option linter.unusedVariables false
32:set_option linter.style.setOption false
33:set_option linter.flexible false
34:set_option linter.unusedSectionVars false
$ sed -n 6p RBM3D/BA/KHeatTail.lean        (sole import)
import RBM3D.BA.KHeat
```
- No new structure or class; the only hypotheses are those in the pinned signature. `BAReal d L g κ E m := BASelf d L g E m ∧ κ ≤ m.im`
  (`MFixedPoint.lean:432`) is a merged definition (the self-consistent equation), not a carrier of the conclusion.
- No external hypothesis: the theorem is deterministic and closed (no limit check needed, TEAM §8 lesson 14 not applicable).
- Dependencies are merged results on `main` (`kBA_diag_le` `KHeat.lean:1221`, `BAK_exp_moment_le` `KKernel.lean:228`,
  `BAP_semigroup_shift`, `BAK_zero_neg`, `BAK_diag`); the file imports only `RBM3D.BA.KHeat`, which cannot import the new file: no cycle.
- Non-vacuity of the hypotheses: they are satisfied at the merged flow point `P` (section 3).
- `set_option` lines are linter switches only.

## 3. Compiled nonempty instance
```
$ sed -n 762,773p RBM3D/BA/KHeatTail.lean   (excerpt)
theorem inst_kBA_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      kBA 3 4 P.g0 P.E P.m0 1 ![1, 0, 2] ≤ C * Real.exp (-c * 3) := by
  obtain ⟨C, c, hC, hc, h⟩ := kBA_le 3 (by norm_num) 10 P.m0.im (by norm_num) P.real.1.1
  ...
  have h1 := h 4 (by norm_num) P.g0 P.E P.m0 P.g0_pos P.g0_le P.real 1 one_pos (by norm_num) ![1, 0, 2]
$ lake env lean ax.lean   (excerpt)
RBM.BA.MFixedPointInst.P : RBM.BA.MFixedPointInst.FlowPt 4 10
@RBM.BA.MFixedPointInst.FlowPt.real : ∀ {L : ℕ} [inst : NeZero L] {g : ℝ} (self : RBM.BA.MFixedPointInst.FlowPt L g),
  RBM.BA.BAReal 3 L self.g0 self.m0.im self.E self.m0
```
Data: `d = 3`, `L = 4` (64 sites), `Λ = 10`, `κ = Im m₀ > 0` (`P.real.1.1`), `(g₀, E, m₀)` the merged flow point `P` of
`MFixedPointInst` (`P.g0_pos`, `P.g0_le : g₀ ≤ 10`, `P.real : BAReal`), `τ = 1 ∈ (0, 16]`, `a = ![1,0,2]` with `zdistD = 3`
(`inst_zdistD` by `decide`). Every hypothesis is discharged; no `N = 0`, empty index, collapsed window or `False` premise; the
instance matches the ticket's "Instances" line exactly. `inst_tail_le` does the same for the helper `BAP_tail_le` (`τ = 1`, `ρ = 2`).
Instances live in the same file and compile (section 4). PASS.

## 4. Build, axioms, diff
```
$ lake build RBM3D.BA.KHeatTail 2>&1 | grep -E "error|KHeatTail|Build"
✔ [3742/3742] Built RBM3D.BA.KHeatTail (6.2s)
Build completed successfully (3742 jobs).
$ lake env lean ax.lean
'RBM.BA.kBA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAP_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatTailInst.inst_kBA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatTailInst.inst_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ git diff --name-status main...t/T2335
A	RBM3D/BA/KHeatTail.lean
$ grep -rn -E "kBA_le|BAP_tail_le|KHeatTail" RBM3D --include='*.lean' | grep -v BA/KHeatTail.lean | grep -v Probe/ | wc -l
       0
```
Only the sole writable file is touched (new); no merged file, so no frozen signature, is changed. Unpinned helpers are `private` with
prefix `KHeatTail_`; the public names (`BAP_tail_le`, `KHeatTailInst.*`) are allowed by the ticket and clash with nothing. The full
`lake build` with `#assert_rbm_axioms` is left to the hub at merge (the prove report pastes a passing registry pre-check).

## 5. Paper deltas
Proposed in the prove report section (d):
- `T2335a` (ticket O4): `A:58-67` walk on `Z^d` read as the centered lift of the torus kernel `K = |M_L|²` (the proof uses the torus
  test function `cosh(λ|x_j|_L)` and builds no lift; recorded).
- `T2335b`: the paper's local CLT `A:62` replaced by `kBA_diag_le` + Chernoff tail + the semigroup splitting of `A:64`.
- `T2335c`: `kBA_le` carries `2 ≤ d`, `3 ≤ L`, `0 < g ≤ Λ`, `BAReal` (its twin `kProd_le` has `1 ≤ d`); `C, c` depend on `(d, Λ, κ)` only.
Every Lean/paper statement difference I found (lift reading, CLT replacement, the `d ≥ 2` and kernel hypotheses, uniformity of the
constants) is covered. The pin itself was set by the dispatcher (supervisor 1048 C1 (i)), so no further candidate is needed.

## 6. Observations (no RETURN)
- The route differs from the ticket's step (1) (no lift of `K` to `Z^d`; the torus Chernoff bound with `cosh(λ|x_j|_L)` instead). The
  ticket allows "work directly with `P_s`"; the statement is unchanged. The prove report records this in (a′) and in `T2335a`.
- Preflight (a) rows 1, 2, 6 describe the lift, which the Lean proof does not build; (a′) corrects this. Report only, no statement effect.
- The route constants are crude (`c_T ≈ 1e-31` at the instance). They are existential in the pin and the instance does not evaluate
  them, so this is not an "astronomically large witness" in the sense of §5.5: the witness data (`L = 4`, `τ = 1`, `a`) are ordinary.

## Verdict
- `kBA_le`: **PASS** (statement equals the pin; no hidden hypothesis, vacuity or cycle; nondegenerate compiled instance; module build
  passes; only standard axioms; diff limited to the sole writable file; paper deltas covered).
- Helper `BAP_tail_le` (not a target): compiles, standard axioms, has an instance.
- Ticket T2335: **PASS**. No dispatcher sign-off needed.
