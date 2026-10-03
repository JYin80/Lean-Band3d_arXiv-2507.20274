Auditor model: claude-opus-5-5

# T2074 audit (round 1) — ST2-18, `RBM3D/Path/NetLift1.lean`

Written Sat Oct  3 20:57:49 UTC 2026. Branch `t/T2074` at `83896d8`, merge base `a84c579`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2074-audit1` (detached).
Targets: `Step2NetLift` (def) / `step2NetLift` (port of RBM2D `Path/NetLift:1334,1387`), and `stNetLift2_part1` (the named part of the pin `STNetLift2`).
Audit check file: `scratchpad/T2074/audit.lean` (contents in §2–§3 below).

## 1. Statement against the pin `STNetLift2` (`Induction/Step2Defs.lean:581`)
```
$ python3 sdiff.py   # whitespace-normalised, split at ' → '
--- pin STNetLift2
+++ stNetLift2_part1
@@ -1 +1 @@
-HEAD Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ
+HEAD ∀ κ ε 𝔡 : ℝ, 0 < κ
@@ -10,4 +10,2 @@
-∀ Cd : ℝ, STStep2LocalPT sz (STflowE z) s t
-STStep2AvgPT sz (STflowE z) s t
-STStep2DecayPT sz Cd (STflowE z) s t
-STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧ STStep2Decay sz Cd (STflowE z) s t
+∀ Cd : ℝ, STStep2DecayPT sz Cd (STflowE z) s t
+STStep2Decay sz Cd (STflowE z) s t 
```
Quantifier prefix (`κ ε 𝔡`, positivity, `𝔠 sz z`, `STFlow`, `0 ≤ s`, `s ≤ t`, `t ≤ lemT z` as `∀ n`, `∀ Cd`) is identical to the pin (DECISIONS §29 boundary forms unchanged). Only change: the two unused per-time hypotheses `STStep2LocalPT`, `STStep2AvgPT` are dropped and only the third conjunct `STStep2Decay` is concluded. Dropping hypotheses strengthens the statement; the conjunct is exactly the pin's. Checked by compiling that part 1 yields the pin's third conjunct under the pin's full hypothesis list, and that part 1 plus any ST2-19 result `Local ∧ Avg` closes `STNetLift2 d`:
```
-- A1
example (d : ℕ) : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
  ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
  ∀ Cd : ℝ, STStep2LocalPT sz (STflowE z) s t → STStep2AvgPT sz (STflowE z) s t →
  STStep2DecayPT sz Cd (STflowE z) s t → STStep2Decay sz Cd (STflowE z) s t :=
  fun κ ε 𝔡 h1 h2 h3 𝔠 sz z hf s t hs hst ht Cd _ _ hD => stNetLift2_part1 d κ ε 𝔡 h1 h2 h3 𝔠 sz z hf s t hs hst ht Cd hD
-- A2
example (d : ℕ) (part2 : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
    STStep2LocalPT sz (STflowE z) s t → STStep2AvgPT sz (STflowE z) s t →
    STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t) : STNetLift2 d := ...
$ lake env lean scratchpad/T2074/audit.lean ; echo exit=$?    (output in §4; exit=0, A1, A2 compile)
```
`Step2NetLift` (`NetLift1.lean:697`) against RBM2D `c9a24cf:Path/NetLift.lean:1334`:
```
$ sed -n 697,700p RBM3D/Path/NetLift1.lean
def Step2NetLift (sz : Sizes d) (E : ℕ → ℝ) (κ τ 𝔡 : ℝ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto → sz.WO 𝔡 → sz.RangeCond τ t →
    STStep2DecayPT sz Cd E s t → STStep2Decay sz Cd E s t
$ git -C ../RBM2D show c9a24cf:RBM2D/Path/NetLift.lean | sed -n 1334,1338p
def Step2NetLift (E : ℕ → ℝ) (κ c τ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    Tendsto d.size atTop atTop →
    Bandwidth d c → CondStInd d E s t → RangeCond d τ t →
    Step2DecayPT d E s t → Step2DecayUnif d E s t
```
Differences: `c`, `Bandwidth`, `CondStInd` dropped (unused; strengthening; T2074a); `sz.WO 𝔡` added (T2074b) — this is an extra hypothesis of the port relative to RBM2D, but it is discharged from `STFlow` (`Admissible`) inside `stNetLift2_part1`, so the pin-level target carries no extra hypothesis. `Tendsto d.size` → `sz.SizeTendsto`, `RangeCond` kept; `Cd` added because the d≥3 control has `((1-s)/(1-u))^{C_d}` (pin's form, any real sign).
Verdict on statement: matches the ticket (named part of `STNetLift2`, proved as `stNetLift2_part1`, as the ticket asks).

## 2. Vacuity, hidden hypotheses, cycles
- `Step2NetLift` is a plain `Prop` implication chain; premises `SizeTendsto` (`Defs/Sizes.lean:173`), `WO` (`:164`), `RangeCond` (`Green/Pins.lean:55`) are merged defs, no new structure, no new fields.
- `stNetLift2_part1` uses only `Green.v3_premises_of_stFlow` (merged) and `step2NetLift` (this file). No dependency on `STNetLift2` or on any ST2-19 name: no cycle.
- The only non-deterministic premise is the pin's own per-time `STStep2DecayPT` (stochastic input of the ST2-04 chain); no external hypothesis is introduced, so no limit check is needed. Registry: one `owed` line for `STStep2DecayPT` (§4).

## 3. Compiled nonempty instances (`NetLift1.lean:879–906`, built in §4)
```
$ sed -n 891,904p RBM3D/Path/NetLift1.lean
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  step2NetLift sz0 (STflowE z0) ((1 / 10) / 2) ((1 / 10) / 2) (1 / 10) sInst tInst Cd
    (by norm_num) (fun n => (RBM.Green.Instance.premises.2.1 n).le) (by norm_num) (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) RBM.Green.Instance.premises.2.2.2.1
    sz0_tendsto flow_z0.1.2.2.2.2 RBM.Green.Instance.premises.2.2.2.2 hD

/-- `stNetLift2_part1` at `d = 3`: `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `sz0`, `z0`, `STFlow`
(`flow_z0`), `0 ≤ s ≤ t ≤ lemT z_n` (`sixteenth_le_lemT`). -/
example (Cd : ℝ) (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  stNetLift2_part1 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) Cd hD
$ grep -n "def sInst\|def tInst\|theorem sz0_values\|theorem flow_z0" RBM3D/Induction/Defs.lean RBM3D/Defs/Sizes.lean
RBM3D/Defs/Sizes.lean:267:theorem sz0_values : sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64 := by
RBM3D/Induction/Defs.lean:435:theorem flow_z0 : STFlow sz0 (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0 :=
RBM3D/Induction/Defs.lean:439:def sInst : ℕ → ℝ := fun _ => 0
RBM3D/Induction/Defs.lean:440:def tInst : ℕ → ℝ := fun _ => 1 / 16
```
Data: `d = 3`, `sz0` (`n=0`: `L=4`, `W=32`, `N=2097152`, `lam=1/64`; `sz0_values`), `z0`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `s ≡ 0 < t ≡ 1/16 ≤ lemT z0`: window not collapsed (audit A3: `example : sInst 0 < tInst 0` compiles), `N ≠ 0`, index sets nonempty, `Cd` arbitrary. Every deterministic hypothesis of `step2NetLift` (`0<κ`, `|E_n| ≤ 2-κ`, `0<τ`, `0≤s≤t<1`, `SizeTendsto`, `WO`, `RangeCond`) and of `stNetLift2_part1` (`STFlow` via `flow_z0`, `t ≤ lemT` via `sixteenth_le_lemT`) is discharged; only `STStep2DecayPT` (an unproved pin of the ST2-04 chain) stays a hypothesis, as CLAUDE.md §4 step 2 allows. Both endpoint theorems: instance present and nondegenerate.

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.Path.NetLift1     (audit worktree)
✔ [3725/3725] Built RBM3D.Path.NetLift1 (12s)
Build completed successfully (3725 jobs).
lake build RBM3D.Path.NetLift1  23.87s user 4.95s system 184% cpu 15.596 total
exit=0
$ grep -c "NetLift1.lean:.*\(error\|warning\)" build.log
0
$ lake env lean scratchpad/T2074/audit.lean; echo exit=$?
'RBM.Ind.Step2NetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.step2NetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stNetLift2_part1' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Path/NetLift1.lean; echo exit=$?
exit=1
$ git diff --stat main...t/T2074
 RBM3D/Path/NetLift1.lean | 908 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   1 +
 2 files changed, 909 insertions(+)
$ git diff main...t/T2074 -- RBM3D/Test/Axioms.lean | grep "^[+-] "
+   `RBM.Gauss.Sizes.STStep2DecayPT, -- `(Eq:Gdecay_w)` per time (`1_2:1349-1351`): hypothesis of `stNetLift2_part1`/`step2NetLift`; proved by the Step 2 chain ST2-04 (T2074, DECISIONS §20 rule: owed)
$ lake build RBM3D && lake env lean precheck.lean   # import RBM3D; import RBM3D.Path.NetLift1; #assert_rbm_axioms (grep)
Build completed successfully (3793 jobs).
axiom audit: 2513 theorems, 1058 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STStep2DecayPT: 1 [no certificate]
premises found by scanning: 82 (borrowed 2, owed 67, structural 13).
exit=0
$ git grep -nwE "def Step2NetLift|theorem step2NetLift|theorem stNetLift2_part1" main -- 'RBM3D/*.lean'; echo exit=$?
exit=1
```
Only the two sole writable files are touched; no merged (frozen) signature changed; the new file imports `Induction.{Step2Defs,Continuity}`, `Propagator.{Deriv,Props4}`, `Loop.KLTree`, not `RBM3D`. Warnings in the build log are in merged upstream files only (0 lines naming `NetLift1.lean`).

## 5. Paper deltas
Lean/paper and Lean/RBM2D statement differences and their coverage (prove report (d), candidates; none yet in `docs/paper-deltas.md`, as expected before merge):
- `Bandwidth`, `CondStInd`, `c` dropped from `Step2NetLift` → `T2074a`.
- `sz.WO 𝔡` added to `Step2NetLift` → `T2074b`.
- `stNetLift2_part1` is the decay conjunct of `STNetLift2` only; the pin closes with ST2-19 → `T2074c`.
- The `STStep2Decay` form itself (`L^∞` block distance, `W^{-D}` floor, `C_d`) is the merged pin of T2066, not changed here.
All differences covered.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The ticket's cut "`1334–1518`" ends at `:1511` (`end MainT1`); the report states the cut and both declaration lists (b.8). For the dispatcher's ST2-19 ticket text.
- O2. `Test/Axioms.lean`: ST2-19 will add adjacent registry lines; a textual conflict is possible at merge (report (d)).
- O3. Prove report b.1 quotes a `simp` linter line from `Step2Defs.lean:978` as the build tail; it is an upstream warning, not one of this file.

## Verdict
- `Step2NetLift` / `step2NetLift`: **PASS**.
- `stNetLift2_part1` (part 1 of `STNetLift2`): **PASS**.
Ticket T2074: **PASS**. No dispatcher sign-off needed.
