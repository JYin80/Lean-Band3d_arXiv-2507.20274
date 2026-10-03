Auditor model: claude-opus-5-5

# T2082 audit (round 1) — ST2-19 `Path/NetLift2`, `stNetLift2_holds : STNetLift2 d`
Time: Sat Oct  3 22:25:37 UTC 2026 (`date -u`). Worktree: `RBM3D-wt/T2082-audit1`, detached at `727236b` (t/T2082).
Scratch: `scratchpad/T2082/{audit.lean,pre.lean}`.

## 1. Files touched, frozen signatures
```
$ git diff --name-only main...t/T2082
RBM3D/Path/NetLift2.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2082 -- RBM3D/Induction RBM3D/Path/NetLift1.lean | wc -l
       0
$ git diff main...t/T2082 -- RBM3D/Test/Axioms.lean   (added lines only)
+   `RBM.Gauss.Sizes.STStep2LocalPT, -- `(Gt_bound_flow)` per time (`1_2:1343`): ... (T2082, DECISIONS §20 rule: owed)
+   `RBM.Gauss.Sizes.STStep2AvgPT, -- `(Gt_avgbound_flow)` per time (`1_2:1345`): ... (T2082, DECISIONS §20 rule: owed)
$ git diff main...t/T2082 | grep -nE "^\+.*\b(sorry|admit|native_decide|axiom )\b"
(no output)
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Path/NetLift2.lean
(no output)
```
Only the two sole writable files; registry edit is two owed lines; the pin file `Induction/Step2Defs.lean` is untouched.

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Path.NetLift2 | grep -iE "error|warning|Build completed"
(warnings only from merged files: LaplaceGauss, HeatProduct, PropUnit, Step34Pins, Walk, Stop, Step2Defs; none from NetLift2)
Build completed successfully (3726 jobs).
$ lake build RBM3D.Test.Axioms
Build completed successfully (2 jobs).
$ lake build RBM3D
Build completed successfully (3819 jobs).
$ lake env lean scratchpad/T2082/audit.lean ; exit=0, error lines: 0
'RBM.Gauss.Sizes.stNetLift2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.step2LocalNetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.step2AvgNetLift' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean scratchpad/T2082/pre.lean   (import RBM3D; import RBM3D.Path.NetLift2; #assert_rbm_axioms) ; exit=0
1:axiom audit: 2543 theorems, 1075 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
61:  RBM.Gauss.Sizes.STNetLift2: 1 [no certificate]
62:  RBM.Gauss.Sizes.STStep2DecayPT: 1 [no certificate]
63:  RBM.Gauss.Sizes.STStep2LocalPT: 0 [no certificate]
64:  RBM.Gauss.Sizes.STStep2AvgPT: 0 [no certificate]
```

## 3. Statements against the pin
Ticket pin: `theorem stNetLift2_holds (d : ℕ) : STNetLift2 d`, "its type exactly", for `Step2Defs.lean:581`.
```
$ (audit.lean) example (d : ℕ) : STNetLift2 d := stNetLift2_holds d      -- elaborates
#check @stNetLift2_holds
stNetLift2_holds : ∀ (d : ℕ), STNetLift2 d
@step2LocalNetLift : ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), Step2LocalNetLift sz E κ τ s t
@step2AvgNetLift : ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), Step2AvgNetLift sz E κ τ s t
#print Step2LocalNetLift
fun {d} sz E κ τ s t => 0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
  (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t → sz.STStep2LocalPT E s t → sz.STStep2Local E s t
#print Step2AvgNetLift
  (same premises) → sz.STStep2AvgPT E s t → sz.STStep2Avg E s t
```
Pin (unchanged on the branch, `Step2Defs.lean:581`): `∀ κ ε 𝔡, 0<κ → 0<ε → 0<𝔡 → ∀ 𝔠 sz z, STFlow sz κ ε 𝔠 𝔡 z →
∀ s t, (∀n, 0 ≤ s n) → (∀n, s n ≤ t n) → (∀n, t n ≤ lemT (z n)) → ∀ Cd, STStep2LocalPT → STStep2AvgPT →
STStep2DecayPT Cd → STStep2Local ∧ STStep2Avg ∧ STStep2Decay Cd` (all at `STflowE z`, `s`, `t`).
- `stNetLift2_holds`: type is the pin verbatim (no extra binder, no specialisation of `d`, `Cd`, `𝔠`; no `3 ≤ d`).
  DECISIONS §29 checks: `0 ≤ s`, `t ≤ lemT z`, `∀ n` all as in the pin (pin's own binders).
- `Step2LocalNetLift` vs RBM2D `c9a24cf:Path/NetLift.lean:1351` (pasted in prove report b.5): the RBM2D
  premises `0 < c`, `Bandwidth d c`, `CondStInd d E s t` are dropped (weaker hypotheses → stronger statement);
  the conclusion is the merged pin `STStep2Local` (squared entry vs `STWB`), not a local redefinition.
  `0 ≤ s`, `s ≤ t`, `t < 1`, `|E| ≤ 2-κ` are `∀ n`, the only limit premise is `SizeTendsto`.
- `Step2AvgNetLift`: same premise list, conclusion the merged pin `STStep2Avg`; no RBM2D source.
Proof assembly (NetLift2.lean:688-695): `⟨step2LocalNetLift …, step2AvgNetLift …, stNetLift2_part1 … hD⟩`
with premises from merged `Green.v3_premises_of_stFlow` at `κ/2`, `ε/2`. Statement: **matches**.

## 4. Hidden hypotheses, vacuity, cycles
- No structure carries a hypothesis: the new definitions are plain `Prop` implications (printed above); the
  only stochastic premises are the per-time pins `STStep2LocalPT/AvgPT/DecayPT` (`PrecPT` =
  `Path.PerTimeDomAt`, `Defs/StochDomAt.lean:125`), which are the pin's own hypotheses, distinct from the
  conclusions (`Prec` = `StochDomAt`, `:121`).
- Dependencies are merged: `stNetLift2_part1` (T2074, NetLift1), `ContinuityNet.cont_core` and friends,
  `Green.v3_premises_of_stFlow`. Nothing assumes `STNetLift2` or a downstream pin: no cycle.
- External hypotheses: none added.

## 5. Compiled nonempty instances (`NetLift2.lean:716-757`, re-elaborated in `audit.lean`)
```
$ (audit.lean, exit 0, 0 errors)
example (Cd : ℝ) (hL : STStep2LocalPT sz0 (STflowE z0) sInst tInst)
    (hA : STStep2AvgPT sz0 (STflowE z0) sInst tInst)
    (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
      STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  stNetLift2_holds 3 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) Cd hL hA hD
#print sInst  => fun x => 0
#print tInst  => fun x => 1 / 16
flow_z0 : sz0.STFlow (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0
'RBM.Gauss.InductionDefsInst.flow_z0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ sed -n 300p RBM3D/Defs/Sizes.lean ; sz0_values (Sizes.lean)
theorem sz0_tendsto : sz0.SizeTendsto
sz0.L 0 = 4 ∧ sz0.W 0 = 32 ∧ sz0.size 0 = 2097152 ∧ sz0.lam 0 = 1 / 64
```
- `stNetLift2_holds` at `d = 3`: every deterministic premise (`0<κ,ε,𝔡`, `STFlow`, `0 ≤ s ≤ t ≤ lemT z`)
  is discharged by merged facts; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_0 = 2^21`, window `[0, 1/16]` not
  collapsed. Only the three per-time pins (ST2-04, owed) stay hypotheses — allowed by CLAUDE.md §4 step 2.
- `step2LocalNetLift`, `step2AvgNetLift`: fully applied examples at `κ = τ = 1/20`, `sz0`, `z0`, `sInst`,
  `tInst`, with `|E| ≤ 2-κ`, `t < 1`, `RangeCond` from `Green.Instance.premises`, `sz0_tendsto`; only the
  per-time pin stays a hypothesis (file lines 724-730, 736-742; the module builds).
Instance: **present and nondegenerate** for every endpoint theorem.

## 6. Paper deltas
Lean/paper differences and their coverage (prove report (d)):
- dropped `c`, `Bandwidth`, `CondStInd`; `STStep2Local` is the squared-entry/`STWB` form → `T2082a`
  (and existing D122 = T2074a for the analogous drop).
- `STStep2Avg` lift new at `d ≥ 3` (no RBM2D counterpart) → `T2082b`.
- Local/Avg lifts carry no `(eq:WO)`, unlike `Step2NetLift` (D123) → `T2082c`.
- `stNetLift2_holds` is the merged pin verbatim, so it introduces no new difference with the pin's own
  deltas (D124 covers the split of the decay conjunct).
Coverage: **complete**.

## 7. Observations (no RETURN)
- O1. `Step2AvgNetLift`/`step2AvgNetLift` are public but not named in the ticket's target list and not
  file-stem prefixed (§3 (E)). They are the endpoint for the `STStep2Avg` conjunct the ticket requires,
  carry instances, and have no clash on `main`
  (`git grep` of the five public names on `main`: only comments in NetLift1.lean:26-27, Step2Defs.lean:579).
  Dispatcher may wish to treat them as de facto pinned names.
- O2. The ticket says `STNetLift2`'s owed registry line "can go once this merges (say so)"; the prover kept
  the line and deferred to the dispatcher (pre-check shows count 1 via `stNetLift2_holds`). Bookkeeping only.
- O3. (a′) records that the Avg lift uses modulus `A = 40` instead of the table's `22`; proof-internal
  constant, no statement effect.

## Verdict
| target | statement | vacuity/cycle | instance | build/axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `stNetLift2_holds : STNetLift2 d` | pin verbatim | none | `d=3`, `sz0`, `[0,1/16]` | pass / 3 std | covered | **PASS** |
| `Step2LocalNetLift` / `step2LocalNetLift` | matches RBM2D port minus unused premises | none | fully applied | pass / 3 std | T2082a | **PASS** |
| `Step2AvgNetLift` / `step2AvgNetLift` | conclusion = merged `STStep2Avg` | none | fully applied | pass / 3 std | T2082b,c | **PASS** |

Ticket T2082: **PASS**. No dispatcher sign-off needed for the verdict (O1, O2 are bookkeeping).
