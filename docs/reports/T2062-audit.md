Auditor model: claude-opus-5-5

# T2062 audit (round 1) — S1-34 `Induction/Continuity` part 2

Written Sat Oct  3 19:20:52 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2062-audit1`,
detached at `030c138` (`t/T2062`); merge-base with `main` = `65ccfb3`. Targets: `gopbound`, `Step1NetLift`/`step1NetLift`,
`stNetLift_holds : STNetLift d`.

## 1. Build, hygiene, scope

```
$ lake build RBM3D.Induction.Continuity   (error/warning lines + tail)
Build completed successfully (3323 jobs).
exit=0
$ grep -nE "sorry|admit|native_decide|^\s*axiom" RBM3D/Induction/Continuity.lean
exit=1            (no hit)
$ git diff --stat main...t/T2062
 RBM3D/Induction/Continuity.lean | 857 ++++++++++++++++++++++++++++++++++++++++
 1 file changed, 857 insertions(+)
$ git diff --stat 65ccfb3 fc76526 -- RBM3D     (main moved since the branch point; no overlap)
 RBM3D/Evolution/Prec.lean       | 657 ++++
 RBM3D/Induction/Step34Pins.lean |   5 +-
```
Only the sole writable file is touched (`RBM3D/Test/Axioms.lean` is unchanged, allowed). Imports:
`RBM3D.Induction.ContinuityNet`, `RBM3D.Induction.Defs`, `RBM3D.Green.Pins` (never `RBM3D`). No frozen signature edited
(new file only).

## 2. Axioms and target types (`scratchpad/T2062/ax.lean`, `lake env lean`, exit 0)

```
'RBM.Ind.gopbound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.step1NetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stNetLift_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
stNetLift_holds : ∀ (d : ℕ), STNetLift d
'RBM.Green.v3_premises_of_stFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
@Green.v3_premises_of_stFlow : ∀ {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}, 0 < κ → 0 < ε →
  sz.STFlow κ ε 𝔠 𝔡 z → ∀ {t : ℕ → ℝ}, (∀ (n : ℕ), t n ≤ lemT (z n)) →
  sz.Admissible 𝔠 𝔡 ∧ (∀ n, |STflowE z n| < 2 - κ / 2) ∧ (∀ n, t n < 1) ∧ sz.RangeCond (ε / 2) t
$ git show main:RBM3D/Green/Pins.lean | grep -n "theorem v3_premises_of_stFlow"
1049:theorem v3_premises_of_stFlow {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
```

## 3. Registry pre-check (`import RBM3D`, `import RBM3D.Induction.Continuity`, `#assert_rbm_axioms`)

```
$ lake env lean scratchpad/T2062/precheck.lean ; echo exit=$?
exit=0
1:axiom audit: 2163 theorems, 884 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
26:  RBM.Gauss.Sizes.STNetLift: 2 [no certificate]
55:premises found by scanning: 45 (borrowed 2, owed 31, structural 12).
66: RBM.Gauss.Sizes.STNetLift,
$ grep -n STNetLift RBM3D/Test/Axioms.lean
102:   `RBM.Gauss.Sizes.STNetLift,      -- net lift of Step 1: S1-34 (T2028, T2015 b.10)
```
The owed line `STNetLift` can be removed by the cleanup ticket after merge (the report says so, (d)).

## 4. Statements against the pins

```
$ sed -n 527p;594,598p;777p RBM3D/Induction/Continuity.lean
theorem gopbound (sz : Sizes d) (κ : ℝ) (E : ℕ → ℝ) : GopboundPin sz κ E := by
def Step1NetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    (STStep1LoopPT sz E s t → STStep1Loop sz E s t) ∧
      (STStep1WeakPT sz E s t → STStep1Weak sz E s t)
theorem stNetLift_holds (d : ℕ) : STNetLift d := by
$ RBM2D c9a24cf Continuity:1261 (git show c9a24cf:RBM2D/Induction/Continuity.lean | sed -n 1261,1265p)
def Step1NetLift (E : ℕ → ℝ) (κ c τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → SizeTendsto d → Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    (Step1LoopPT d E s t → Step1LoopUnif d E s t) ∧
      (Step1WeakLawPT d E s t → Step1WeakLawUnif d E s t)
```
- `gopbound`: type is literally the merged pin `GopboundPin sz κ E` (`ContinuityNet.lean:55`, T2047), all `d`.
  RBM2D `Continuity:1269` has the same shape with `d : Sizes`; witness `C' = 2C+14` unchanged (dimension-free:
  `N = (WL)^d` only). **PASS.**
- `stNetLift_holds`: `#check` gives `∀ (d : ℕ), STNetLift d`, the merged pin (`Defs.lean:377`) exactly; no `3 ≤ d`,
  no added hypothesis. The pin's premise `hu` (Prec at every time *sequence*, union over `(σ,a)` in `P`) is
  turned into `STStep1LoopPT` (`PrecPT` over `TimeIcc × (σ,a)`, `Defs.lean:248`) by the private
  `perTime_of_sections` (proved, via `perTimeDomAt_iff_forall_section`, `StochDomAt.precomp_param`); the
  deterministic premises come from the merged theorem `v3_premises_of_stFlow` at `(κ/2, ε/2)`. **PASS.**
- `Step1NetLift`/`step1NetLift`: after renaming R1–R4 the only differences from RBM2D are the dropped
  `c`, `0 < c`, `Bandwidth d c`, `CondStInd d E s t` (strictly fewer hypotheses: a stronger statement) and the
  merged ST vocabulary `STStep1LoopPT/Loop`, `STStep1WeakPT/Weak`, `Sizes.RangeCond`. Both halves are kept.
  Covered by paper-delta candidate `T2062a` (report (d)). Not a pin of any downstream ticket (`stNetLift_holds`
  is the pinned endpoint). **PASS.**

Dropped declarations (report b.6): `cont_llErr_diff`, `cont_scaleM_ratio`, `cont_one_le_size` — all `private`
in RBM2D, so no later ticket can consume them. No dispatcher decision needed.

## 5. Hidden hypotheses, vacuity, cycles

- No `structure`/`class` is declared in the file (declaration list: `grep -nE "^(private )?(theorem|def|structure|class|…)"`
  shows 17 private theorems/defs, 3 public theorems, 1 public `def Step1NetLift`, 5 `example`s).
- No cycle: `stNetLift_holds` uses `STNetLift` only as its conclusion; non-comment occurrences of pin names:
  ```
  527:theorem gopbound (sz : Sizes d) (κ : ℝ) (E : ℕ → ℝ) : GopboundPin sz κ E := by
  777:theorem stNetLift_holds (d : ℕ) : STNetLift d := by
  780:  have hPT : STStep1LoopPT sz (STflowE z) s t := by
  ```
  Every dependency (`ContinuityNet` T2047, `Induction.Defs`, `Green.Pins` T2028) is merged on `main`.
- No external hypothesis is introduced; no PT/propagator pin occurs in this part.

## 6. Compiled nonempty instances (file section 5, lines 809–854; compiled in §1 build)

Concrete data (from `#print`, §2 script):
```
def RBM.Gauss.InductionDefsInst.sInst : ℕ → ℝ := fun x => 0
def RBM.Gauss.InductionDefsInst.tInst : ℕ → ℝ := fun x => 1 / 16
def RBM.Gauss.InductionDefsInst.z0 : ℕ → ℂ := fun n => { re := 1 / 2, im := ↑(sz0.size n) ^ (-(4 / 5)) }
flow_z0 : sz0.STFlow (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0
sixteenth_le_lemT : ∀ (n : ℕ), 1 / 16 ≤ lemT (z0 n)
Green.Instance.premises : sz0.Admissible (1 / 6) (1 / 10) ∧ (∀ n, |STflowE z0 n| < 2 - 1 / 10 / 2) ∧
    (∀ n, 0 ≤ tInst n) ∧ (∀ n, tInst n < 1) ∧ sz0.RangeCond (1 / 10 / 2) tInst
```
`sz0`: `d = 3`, `n = 0`: `L = 4`, `W = 32`, `N = 2^21`; window `[0, 1/16]` nondegenerate.
- `gopbound` (line 809): applied to `sz0`, `κ = 1/10`, `E ≡ 1/2`, `0 < κ`, `|E| ≤ 2-κ`, `sz0_tendsto` all discharged;
  `C` with `0 < C` is the pin's own universally quantified parameter. Nondegenerate. **PASS.**
- `step1NetLift` (line 822): all eight deterministic premises discharged at `sz0`, `STflowE z0`, `κ = τ = 1/20`,
  `sInst`, `tInst`; the conclusion's implications keep `STStep1LoopPT/WeakPT` as antecedents (the stochastic
  input of the statement itself). **PASS.**
- `stNetLift_holds` (lines 833, 844): `stNetLift_holds 3` applied with `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `flow_z0`,
  `0 ≤ s`, `s ≤ t`, `t ≤ lemT z0` all discharged; only `hu` (the pin's own stochastic premise, the same as the
  merged `inst_netLift`, `Defs.lean:607`) stays. No `N = 0`, no empty index, no collapsed window, no `False`
  premise. **PASS.**

## 7. Paper deltas

- `T2062a` (Step1NetLift drops `c`, `Bandwidth`, `CondStInd`; ST vocabulary) is proposed in the prove report (d).
- `gopbound` and `stNetLift_holds` have the merged pins' types exactly: no new Lean/paper difference.
Coverage complete.

## 8. Observations (no RETURN)

- O1. Pre-check theorem count here is 2163 vs 2158 in the prove report b.3: the copied `.lake/build` root olean
  is from current `main` (`fc76526`, includes T2053), not the branch base `65ccfb3`. Premise counts (45, `STNetLift`
  without certificate) agree.
- O2. The `gopbound` example keeps `C` as a variable with `0 < C`; instantiating `C = 1` would be marginally more
  concrete. Not a defect (the pin quantifies over `C`).

## Verdict

| Target | Verdict |
|---|---|
| `gopbound : GopboundPin sz κ E` | PASS |
| `Step1NetLift` / `step1NetLift` | PASS (delta `T2062a`) |
| `stNetLift_holds : STNetLift d` | PASS |

Ticket T2062: **PASS**. No dispatcher sign-off needed.
