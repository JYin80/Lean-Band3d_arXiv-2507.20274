Auditor model: claude-opus-5-5

# T2369 audit (round 1) — Sat Oct 10 05:36:54 UTC 2026

Branch `t/T2369` at `424828c`; audit worktree `RBM3D-wt/T2369-audit1` (detached, fresh build cache). Scratch: `<scratchpad>/T2369/`.

## 1. Diff scope, hygiene, stop line
```
$ git diff --name-only main...t/T2369
RBM3D/BA/KWard.lean
RBM3D/Loop/KLWard.lean
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide" RBM3D/Loop/KLWard.lean RBM3D/BA/KWard.lean ; echo grep-exit=$?
grep-exit=1
$ (public names of main:KLWard.lean, count of declarations with that name on the branch)
KLWard_flip 1 / KLK_ward 1 / KLWardInst_ward_true 1 / KLWardInst_ward_false 1 / KLWardInst_ward_two_false 1 / KLWardInst_ward_four_false 1 / KLWardInst_flip 1
growth: KLWard +200 (1424 vs base 1224), KWard 399, total 599 (stop line 1000)
```
Only the two sole writable files; no public name deleted or renamed; `Test/Axioms.lean` untouched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Loop.KLWard RBM3D.BA.KWard
✔ [3733/3740] Built RBM3D.Loop.KLWard (9.7s)
✔ [3740/3740] Built RBM3D.BA.KWard (3.5s)
Build completed successfully (3740 jobs).   exit=0
$ lake env lean audit.lean   (#print axioms)
'RBM.Loop.wardS_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.kernelFacts_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.kernelFacts_SB' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLK_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWard_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Loop.KLWardInst_wardS' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baK_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
audit-exit=0
```

## 3. Target 1: pins `KernelFacts`, `WardS`
```
$ diff <(sed -n '/^structure KernelFacts/,/^$/p' check.lean) <(sed -n '/^structure KernelFacts/,/^$/p' RBM3D/Loop/KLWard.lean) && echo KernelFacts-identical
KernelFacts-identical
$ diff <(sed -n '/^def WardS/,/^$/p' check.lean) <(sed -n '/^def WardS/,/^$/p' RBM3D/Loop/KLWard.lean) && echo WardS-identical
WardS-identical
```
Lean checks in `audit.lean` (exit 0, above): the check file's `WardS` text copied into `namespace RBM.Loop.AuditCopy` as `WardS'` with
`example : WardS' = RBM.Loop.WardS := rfl`; the check file's `KernelFacts` re-declared in `RBM.Loop.AuditKF` with
`RBM.Loop.KernelFacts S ↔ KernelFacts S := ⟨fun h => ⟨h.symm, h.real, h.colSum, h.entry⟩, fun h => ⟨…⟩⟩`. Field by field:
```
$ #print RBM.Loop.KernelFacts
  RBM.Loop.KernelFacts.symm : ∀ (a b : RBM.Zd d L), S a b = S b a
  RBM.Loop.KernelFacts.real : ∀ (a b : RBM.Zd d L), (starRingEnd ℂ) (S a b) = S a b
  RBM.Loop.KernelFacts.colSum : ∀ (b : RBM.Zd d L), ∑ a, S a b = 1
  RBM.Loop.KernelFacts.entry : ∀ (a b : RBM.Zd d L), ‖S a b‖ ≤ 1
```
Four fields = the four band facts the ticket names (`SB_transpose`, `conj SB = SB`, `sum_SB_row`, `norm_SB_apply_le`); no further field, no
hidden hypothesis. Verdict target 1: **PASS**.

## 4. Target 2: `wardS_holds : WardS`
```
RBM.Loop.wardS_holds : RBM.Loop.WardS
```
Statement is the pin itself (rfl above). Hypotheses of `WardS` vs ticket mathematics: `KernelFacts S`, `1 ≤ W`, `Im m(+) > 0`,
`m(-) = conj m(+)`, flip of `M` (lengths `≥ 2`), rotation of `M`, `t = 0` identity on lengths `|μ| ≥ 1` (loops `≥ 3`), level-2 identity of the
family; conclusion `(WI_calK)` with `η_t = (1-t) Im m(+)` for all `t ∈ [0,1)`, `s`, `μ`, `a.length = μ.length + 1`. `‖m‖ = 1` is not a hypothesis
(as the ticket requires). Non-vacuity: `KLWardInst_wardS` (KLWard.lean:1408) applies `wardS_holds` with **every** hypothesis discharged at
`d=3, L=5, W=2, S=SB 3 5 (1/2), m=mSigma 0, M=MLoop, K=KLK, t=9/10`, loop `(+,-,-)`, `a=(0,1,x)`; it compiles (build above, axioms above).
Dependencies (`uniqS_holds`, `retireS_holds`, `rotS_holds`, `KLK_isKLoop`, `KLward_two`) are on `main`; no cycle (the module imports only
merged modules and `wardS_holds` is proved before its band consumers). Verdict target 2: **PASS**.

## 5. Target 3: band instances and G1
```
@RBM.Loop.kernelFacts_one : ∀ {d L : ℕ} [inst : NeZero L], RBM.Loop.KernelFacts 1
@RBM.Loop.kernelFacts_SB : ∀ {d L : ℕ} [inst : NeZero L] (g : ℝ), 3 ≤ L → RBM.Loop.KernelFacts (RBM.SB d L g)
$ cd RBM3D-wt/T2369-audit1 && lake env lean docs/tickets/checks/T2369-check.lean ; echo check-exit=$?
(… #check output of IsKLoopS, IsKLoop_iff_IsKLoopS, KLK_isKLoop, KLward_two, SB_transpose, Gauss.etaT …)
check-exit=0
```
Signatures match probe 211/218 (`kernelFacts_SB` carries `3 ≤ L` as in the probe). Part 2 of the check (`KLK_ward`, `KLWard_flip` with the
old statements, by `@name`) elaborates on the branch: G1 holds. `KLK_ward` is now `wardS_holds` at `SB`, `mSigma E`, `MLoop`
(KLWard.lean:1318-1330); `KLWard_flip` is `KLWard_K_flip` at the same data. Instances: `KLWardInst_ward_{true,false,two_false,four_false}`,
`KLWardInst_flip`, `KLWardInst_kernelFacts_one` (`Zd 3 5`), `KLWardInst_kernelFacts_SB` (`SB 3 5 (1/2)`, `3 ≤ 5` discharged) all compile.
Verdict target 3: **PASS**.

## 6. Target 4: `baK_ward` (`RBM3D/BA/KWard.lean:305`)
```
RBM.BA.baK_ward : ∀ (d L W : ℕ) [inst : NeZero L] (g κ E : ℝ) (m : ℂ),
  RBM.BA.BAReal d L g κ E m → 3 ≤ L → 1 ≤ W →
    ∀ {K}, RBM.Loop.IsKLoopS d L W 1 (RBM.PropSpin m)
              (RBM.BA.BAMLoop d L W (RBM.BA.BAMsigma d L (RBM.BA.BAMB d L g (↑E) m))) (Set.Ico 0 1) K →
      (∀ t ∈ Set.Ico 0 1, ∀ (σ : Bool × Bool) (a₁ a₂ : RBM.Zd d L),
          K t { σ := [σ.1, σ.2], a := [a₁, a₂] } =
            (↑W ^ d)⁻¹ * (RBM.BA.BATheta d L g E m t σ.1 σ.2 * RBM.BA.BAMss d L (RBM.BA.BAMB d L g (↑E) m) σ.1 σ.2) a₁ a₂) →
      ∀ t ∈ Set.Ico 0 1, ∀ (s : Bool) (μ : List Bool) (a : List (RBM.Zd d L)), a.length = μ.length + 1 →
        ∑ x, K t { σ := s :: μ ++ [!s], a := a ++ [x] } =
          (2 * Complex.I * ↑W ^ d * ↑((1 - t) * (RBM.PropSpin m true).im))⁻¹ *
            (K t { σ := true :: μ, a := a } - K t { σ := false :: μ, a := a })
$ lake env lean ps.lean   # example (m : ℂ) : RBM.PropSpin m true = m := rfl ; … PropSpin m false = conj m := rfl
(both examples elaborate; only error is line 4 '#print axioms RBM.BA.BAKsolve', unknown on the branch base a5c1a1a)
```
The `(Kn2sol)` hypothesis is textually the second conjunct of `BAKsolve` (probe `T2360Pins.lean:281` and merged `main:RBM3D/BA/KSolve.lean:65-67`,
compared by eye: identical up to binder names). Hypotheses = exactly those the ticket lists; conclusion = `WardS` conclusion at `m true = m`
(`PropSpin m true = m` by `rfl`). Proof is `wardS_holds` at `S = 1` with every `WardS` hypothesis discharged by private lemmas whose
signatures carry only `BAReal`, `1 ≤ W`, `(Kn2sol)` (KWard.lean:227, 271). Private rotation helper is `BAKWard_BAMLoop_rot` (not K03's name).
Instances (KWard.lean:341-394, compile): `BAKWard_zero`, flip, rotation of `BAMLoop` at the merged flow point `P` (`d=3, L=4, W=2`,
`P.real : BAReal`), loops of length 3–4 with distinct labels, unconditional; the level-2 consequence `BAKWard_two` with an explicit family
`BAKWardInst_K2` (`(Kn2sol)` by `rfl`), all `t ∈ [0,1)`, all `a`; `baK_ward` itself at `P`, `t = 1/2`, `(+,[-],(0,e₁))` with `hK`, `hn2` as
hypotheses. Those two are the `BAKsolve` existence pin, an owed prop on `main` (`Test/Axioms.lean:141`, owed: BA-K05b); `baKsolveLe3_holds`
(T2368, merged after the branch base) yields only `IsKLoopSLe … 3`, so it could not discharge `hK`. Every deterministic hypothesis
(`BAReal`, `3 ≤ 4`, `1 ≤ 2`, `t ∈ [0,1)`, `a.length = μ.length + 1`) is discharged. This is the ticket's stated fallback. Verdict target 4: **PASS**.

## 7. External hypotheses / limit checks
No external input. `WardS`'s `t = 0` and level-2 hypotheses are discharged in both instances (band: `KLWard_band_zero`, `KLWard_band_two`; BA:
`BAKWard_zero`, `BAKWard_two`), so they are proved, not assumed. The N2 table (prove report b7: max `t = 0` defect `3.3e-16`, max `(WI_calK)`
`2.2e-9`) is below the `1e-6` stop line and the `1e-8` target.

## 8. Paper-delta coverage
Lean/paper differences and their candidates (prove report §(d)): general kernel `WardS` (T2369a); `t = 0` step via the entrywise resolvent
identity, not `BAMB_ward_row` alone (T2369b); `‖m‖ = 1` dropped (T2369c); level-2 input stated as `∑_x K^{(2)}_{(+,-),(a,x)} = (W^d(1-t))⁻¹`
(T2369d); `baK_ward` takes `(Kn2sol)` as a hypothesis, `3 ≤ L` unused (T2369e). The band statements `KLK_ward`, `KLWard_flip` are unchanged
(check Part 2). Every statement difference is covered.

## 9. Observations (no verdict effect)
- O1. Ticket (target 4) says `BAMB_ward_row` closes the `t = 0` step; the proof uses the stronger entrywise identity `M - M^* = 2i Im m M^*M`
  (`BAKWard_resolvent`, KWard.lean:189). Route only; recorded as T2369b.
- O2. For K12: merged `BAKsol_isKLoopS` drops the `(Kn2sol)` conjunct, so `BAKward` needs `(Kn2sol)` for `BAKsol` transferred by uniqueness
  (prove report §(d), b8). Dispatcher information; not a defect of this ticket.
- O3. `hL : 3 ≤ L` in `baK_ward` is unused (required by the ticket's statement; T2369e).

## Verdict
| Target | Verdict |
|---|---|
| 1 `KernelFacts`, `WardS` (pins) | PASS |
| 2 `wardS_holds` | PASS |
| 3 `kernelFacts_one`, `kernelFacts_SB`, `KLK_ward`, `KLWard_flip` (G1) | PASS |
| 4 `baK_ward` | PASS |

**T2369: PASS.** No dispatcher sign-off needed.
