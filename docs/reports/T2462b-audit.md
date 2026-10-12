Auditor model: claude-opus-5-5

# T2462b (U4s1b) audit, round 1 — Mon Oct 12 19:27:52 UTC 2026 (`date -u`)
Scope: targets 8-11 (`Chain/Step5KerGen`, `Chain/NewKLKLGen`) under Amend 1 (R1, item 5) and the amended check
`docs/tickets/checks/T2462-check.lean` (b6821280). `t/T2462b` = 763208b4 (base c9f69dba); worktree `RBM3D-wt/T2462b-audit1`. U4s1a is merged, not audited.

## 1. Build, hygiene, diff
```
$ lake build RBM3D.Chain.Step5KerGen RBM3D.Chain.NewKLKLGen ; echo exit=$?
✔ [3801/3802] Built RBM3D.Chain.NewKLKLGen (7.1s)
✔ [3802/3802] Built RBM3D.Chain.Step5KerGen (11s)
Build completed successfully (3802 jobs).
exit=0
$ grep -c "Chain/Step5KerGen.lean:\|Chain/NewKLKLGen.lean:" build.txt     # warnings/errors in the two files
0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " <two files>; echo grep=$?
grep=1
$ git diff --stat main...HEAD
 RBM3D/Chain/NewKLKLGen.lean  | 377 +++++
 RBM3D/Chain/Step5KerGen.lean | 550 +++++
 2 files changed, 927 insertions(+)
$ grep -n "^import\|^open private" <two files>
Step5KerGen.lean:6:import RBM3D.Chain.Step5Gen
Step5KerGen.lean:7:import RBM3D.Induction.Step5Kernel
Step5KerGen.lean:39:open private step5Ker_tailW_eq step5Ker_zdistInf_sub_comm from RBM3D.Induction.Step5Kernel
NewKLKLGen.lean:6:import RBM3D.Chain.Step5Gen
NewKLKLGen.lean:7:import RBM3D.Chain.NewKLKGen
NewKLKLGen.lean:8:import RBM3D.Induction.NewKLKL
NewKLKLGen.lean:35:open private newKLKL_Cs_ge_one newKLKL_tailT_le_tailW newKLKL_tailW_eq_of_near newKLKL_tailW_of_far
NewKLKLGen.lean:37:open private NewKLKGen_conv_two NewKLKGen_ward_LKM from RBM3D.Chain.NewKLKGen
$ git grep -F -w <9 new public names> main -- RBM3D | wc -l   (main = 03109267)  -> 0 for each of the 9 names
```
Only the two new sole writable files are touched (both new: no frozen signature, no `Induction/*`, `Carrier`, `Step2Gen`,
`Step2Kern`, `GridDuhamelGen`, `NewKLKGen`, `Step5Gen`, `BA/*` edit); imports equal the ticket's Layout; no direct `BA/*`
import; no registry line (Amend 1 item 6). Lines 550 / 377 < 2,000.

## 2. Statements against the pins (typed examples + text diff)
Scratch `audit_pins.lean` = the check file's imports + `Chain.Step5KerGen` + `Chain.NewKLKLGen`, the check's Part 1-2 body
verbatim (incl. all BA shape lines), then:
```
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : T2462_uKerDecomp C n := Step5KerGen_uKer_eq C n
example {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : T2462_UNDecomp C n := Step5KerGen_UN_decomp C n
example : @T2462_ThDecayK = @Step5KerGen_ThDecay := rfl
example : T2462_ThDecayK_band := step5KerGen_thDecay_band
example (d : ℕ) : T2462_ProfileK d := step5KerGen_profile_holds d
example (d : ℕ) (mk : ∀ sz : Sizes d, (ℕ → ℝ) → Step2Mat sz) : T2462_stNewKLKLgL'_of d mk := stNewKLKLgL'_of d mk
example (d : ℕ) : T2462_NewKLKL_band d := stNewKLKLgL'_holds_band d
example (d : ℕ) : T2462_TailtoTail_band d := stTailtoTailgL'_holds_band d
$ lake env lean audit_pins.lean > audit_pins.out; echo exit=$?; grep -c error audit_pins.out
exit=0
0
$ python3 -I sdiff.py <check> Step5KerGen.lean NewKLKLGen.lean   (whitespace-normalized; pin body vs statement tail)
T2462_uKerDecomp -> Step5KerGen_uKer_eq: pin body is the statement tail=True | binders: '{d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop' vs '(C : FlowFM sz) (n : ℕ) :'
T2462_UNDecomp -> Step5KerGen_UN_decomp: pin body is the statement tail=True | binders: (same; {d} {sz} are section variables, :52)
T2462_ThDecayK -> Step5KerGen_ThDecay: header+body identical=True
T2462_ThDecayK_band -> step5KerGen_thDecay_band: pin body is the statement tail=True | binders: ': Prop' vs ':'
T2462_ProfileK -> step5KerGen_profile_holds: pin body is the statement tail=True | binders: '(d : ℕ) : Prop' vs '(d : ℕ) :'
T2462_stNewKLKLgL'_of -> stNewKLKLgL'_of: pin body is the statement tail=True | binders identical
T2462_NewKLKL_band -> stNewKLKLgL'_holds_band: pin body is the statement tail=True | binders: '(d : ℕ) : Prop' vs '(d : ℕ) :'
T2462_TailtoTail_band -> stTailtoTailgL'_holds_band: pin body is the statement tail=True | binders: '(d : ℕ) : Prop' vs '(d : ℕ) :'
```
- Target 9's comparison is R1 verbatim (`Step5KerGen.lean:310`); quantifier order `∀ Λ C₆ A … ∃ Cp, ∀ sz C gK …` as pinned
  (constants before the size sequence); window disjunction, `0 ≤ u ≤ t < 1`, `0 < gK n ≤ Λ` as pinned.
- `stNewKLKLAtgL'_of` (unpinned public helper of target 10): `(hd : 3 ≤ d) κ 𝔡 (hκ : 0 < κ) mk (hyp : NewKLKGenHyp d κ 𝔡 mk) :
  ∃ C, 0 < C ∧ STNewKLKLAtgL' d κ 𝔡 C (κ / 2) mk` — U6's merged pointwise pin, δ₀ = κ/2 explicit; used by target 10.

## 3. Axioms (from `audit_pins.out`)
```
'RBM.BA.Step5KerGen_uKer_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step5KerGen_UN_decomp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Step5KerGen_ThDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.step5KerGen_thDecay_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.step5KerGen_profile_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stTailtoTailgL'_holds_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKLAtgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKLgL'_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stNewKLKLgL'_holds_band' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 4. Hidden hypotheses, vacuity, cycles
```
$ grep -n "structure FlowFM" -A 12 RBM3D/Chain/Carrier.lean | grep " : "     # carrier fields: data only
  L : ∀ (n : ℕ) (t : ℝ) {k : ℕ}, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → sz.SeqΩ → ℂ
  K … ; G … ; M … ; S : ∀ n : ℕ, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ ; eta : ∀ (n : ℕ) (t : ℝ), ℝ   (no Prop field)
$ grep -n "def NewKLKGenHyp\|def Step2Gen_USemigroup" RBM3D/Chain/*.lean
GridDuhamelGen.lean:51:def Step2Gen_USemigroup …      NewKLKGen.lean:383:def NewKLKGenHyp …   (both merged)
```
Premises are explicit: `Step2Gen_USemigroup` (band `step2Gen_USemigroup_band`), `Step5KerGen_ThDecay` (band target 9),
R1 (band `gK = sz.lam, A = 1`; non-band `lam/2, A = 4`), `NewKLKGenHyp` (band `newKLKGenHyp_band`, merged). Each is
discharged at concrete data in §5. Imports: both modules sit on merged files only; reverse cones empty (prove E1), so no cycle.

## 5. Compiled nonempty instances (in the files; compiled by the build in §1)
| target | file:line | data | deterministic hypotheses discharged |
|---|---|---|---|
| 8 uKer | `Step5KerGen:412` | `bandFM sz0 0`, n=0, (+,-), s=1/4, t=1/2 | semigroup by `step2Gen_USemigroup_band`, `0≤t<1` |
| 8 UN | `Step5KerGen:418` | k=2, σ=(+,-), any A, a | same |
| 8 band re-derivation | `Step5KerGen:429` | any `sz`, `|E n|≤2`, 0<t<1 | gives `step5Kernel_decompU` form |
| 9 ThDecay band | `Step5KerGen:453` | Λ=4, sz0, E=0 | `|E n|≤2` |
| 9 profile, band | `Step5KerGen:461` | gK=sz0.lam=1/64, A=1, W=32, D=2, u=0, t=1/2 | ThDecay, R1, `0<gK≤Λ`, window `1/65536≤1/2` |
| 9 profile, non-band | `Step5KerGen:499` | kernel at lam/2 (`carrierH`), gK=sz0.lam/2≠sz0.lam, A=4 | ThDecay (band thm at `szH`), R1 (positivity/nlinarith), window |
| 10 generic→band | `NewKLKLGen:329, 334` | d=3; U6 route | `newKLKGenHyp_band` |
| 10 pointwise | `NewKLKLGen:337, 353` | κ=𝔡=1/10, δ₀=1/20, sz0, n=0, E=0, u=1/32, D=1, H=0 | `lam≤κ⁻¹`, `κ≤Im m`, Hermitian H, `‖G−M‖≤1/31≤1/20` |
| 11 band | `Step5KerGen:523` | E=0, D=2, s=1/2, t=3/4, σ=(+,-), nonzero tensor | `lam²≤1−t`, `κ≤Im m` |
sz0 at n=0: L=4, W=32, lam=1/64 (`sz0_values`): no N=0, empty index, collapsed window or False premise. Amend 1 item 5 met
(no `withLam`; non-band coupling below `sz.lam`). No example leaves an unproved gate pin as hypothesis.

## 6. Target 12 greps (all three Chain files)
```
$ grep -nE "withLam|lam0|BAflowLam0|seqHflowBA" Step5CasesGen Step5KerGen NewKLKLGen; echo exit=$?
exit=1
$ grep -nF "∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2" <3 files>
Step5KerGen.lean:305:`∀ n, 0 ≤ gK n * sz.lam n ∧ …` (docstring)
Step5KerGen.lean:310:      (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
$ grep -nw gK <3 files>   -> only Step5KerGen.lean 23,25 (header), 185-191 (ThDecay def), 239, 303-321 (profile), 458,477,496-497 (instances)
$ grep -nE "gK n ≤ sz.lam|≤ A \* gK|sz.lam n \^ 2 ≤ A" <3 files>   -> only :305, :306 (docstring), :310
$ grep -nE "Ring.inverse|Matrix.of|cycProd" <2 files>; echo exit=$?            -> exit=1
$ grep -nE "(def|theorem|lemma|abbrev) [A-Za-z_']*Ugen" <2 files>; echo exit=$?  -> exit=1
$ grep -nE "RBM\.UN|\bUN d|uKer d|Theta d|thetaKer d|Ugen" <2 files>
Step5KerGen.lean:167-171 (private band row helper), 200-234 (private Step5KerGen_theta_decay_band), 431-446 (band example)
```
(a): declarations reading `gK` = `Step5KerGen_ThDecay` (decay only, no crossing) and `step5KerGen_profile_holds` (carries R1).
Private `Step5KerGen_cmp_pos` (:263) is Amend 1 item 3's per-index lemma; private `Step5KerGen_tailT_cross` (:275) takes its
output on bare variables. (b): pattern hits (prove E5, consistent with the (c) lines above) are band helpers, band results and
instances only. (c): clean; no kernel or `Ugen` defined.

## 7. Paper deltas
`docs/paper-deltas.md` has no T2462 entry yet; the prove report §(d) proposes three candidates covering every difference:
- `T2462b·a` (target 9): decay at `gK`, profile/windows at `sz.lam`, joined by R1; all charge pairs (paper: (+,−) only,
  `3_5_Loop_Hierarchy.tex:2058` `uwp2-92kj`); explicit `Cp`.
- `T2462b·b` (target 8): `eq:decompUalt` (`A_deterministic_estimates.tex:100`, checked: `… = 1 + Ξ`, `Ξ = (t−s)·…`) under
  `Step2Gen_USemigroup`; the `s/t + ((t−s)/t)Θ_t` form only at the band.
- `T2462b·c` (target 10): `lem:newKLK` at ℓ = L under `NewKLKGenHyp` (F5, F8, F9 read), δ₀ = κ/2, explicit C.
Target 11 is a band instance of U6's merged pin (no new difference). Coverage complete.

## 8. Observations (no statement, instance, build, axiom or coverage effect)
- O1. Candidate tags are `T2462b·a/b/c` rather than the `T####a` form; the dispatcher numbers them anyway.
- O2. `NewKLKLGen.lean:37` opens privates `NewKLKGen_conv_two`, `NewKLKGen_ward_LKM` of `Chain/NewKLKGen`; a later rename
  there breaks this file (prove report (d)1).
- O3. Transitive `BA.FlowPins`/`BA.MFixedPoint` via `Chain/NewKLKGen` (note (9)). O4. Check cites `uwp2-92kj` at `3_5:2048-2053`; label is `:2058`.
- O5. BA readings (R1 at `BAflowLam0`, `A = (κ+1)/κ`) are shapes only; they elaborate in the scratch (check lines 345-353).

## Verdict
- Target 8 (`Step5KerGen_uKer_eq`, `Step5KerGen_UN_decomp`): **PASS**
- Target 9 (`Step5KerGen_ThDecay`, `step5KerGen_thDecay_band`, `step5KerGen_profile_holds`): **PASS**
- Target 10 (`stNewKLKLAtgL'_of`, `stNewKLKLgL'_of`, `stNewKLKLgL'_holds_band`): **PASS**
- Target 11 (`stTailtoTailgL'_holds_band`): **PASS**
- Target 12 greps, target 13 instances: **PASS**

**T2462b: PASS.** No dispatcher sign-off needed. The hub's full `lake build` runs at merge (two new root imports).
