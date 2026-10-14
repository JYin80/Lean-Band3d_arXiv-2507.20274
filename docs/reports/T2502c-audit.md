Auditor model: claude-opus-5-5

# T2502c audit (round 1) — T2502 row c, `RBM3D/Chain/ExpAvgGen.lean`, under Amend 1 (sign-off (A), per-time form)
Written Wed Oct 14 09:46:30 UTC 2026 (`date -u`). Branch `t/T2502c` head `7cf02a5f`; audit worktree `RBM3D-wt/T2502c-audit1` (detached).
Binding texts: `docs/tickets/checks/T2502-amend-1-check.lean` (name map `T2502_X ↦ ExpAvgGen_X`, `T2502_ImproveCoregL ↦ STImproveCoregL`).
Scratch (uncommitted): `<scratchpad>/T2502c/defdiff.py`, `<scratchpad>/T2502c/Audit.lean` (= the Amend 1 check with `import RBM3D.Chain.ExpAvgGen` plus the examples below).

## 1. Diff, size, imports
```
$ git diff --stat main...t/T2502c
 RBM3D.lean                 |    1 +
 RBM3D/Chain/ExpAvgGen.lean | 1587 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2502Pins.lean |  291 ++++++++
 RBM3D/Test/Axioms.lean     |    5 +-
$ git diff --stat main...t/T2502c -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Gauss RBM3D/Evolution RBM3D/Chain/Step6Gen.lean RBM3D/Chain/Step6KitGen.lean RBM3D/Chain/ExpHierGen.lean RBM3D/Chain/ExpDuhamelGen.lean | wc -l
       0
$ wc -l RBM3D/Chain/ExpAvgGen.lean            # stop line 1,750 (Amend 1 item 5)
    1587 RBM3D/Chain/ExpAvgGen.lean
$ grep -n "^import" RBM3D/Chain/ExpAvgGen.lean   # no BA/*, no Chain/Step2Kern (Amend 1 item 6)
6:import RBM3D.Chain.Step6KitGen
7:import RBM3D.Induction.ExpAvg
8:import RBM3D.Chain.CltGen
9:import RBM3D.Evolution.XiPins
$ grep -rln "import RBM3D.Probe.T2502Pins" RBM3D RBM3D.lean | wc -l
       0
$ grep -nE "^(noncomputable )?(def|abbrev|structure) " RBM3D/Chain/ExpAvgGen.lean | wc -l   # = the 9 defs of Amend 1 item 3
       9
```
`RBM3D.lean`: one line `+import RBM3D.Chain.ExpAvgGen` after the last import (before `#assert_rbm_axioms`). `Test/Axioms.lean`: registry lines
only (`owedProps`: owner text of `STImproveExpAvergL` edited; `ExpAvgGen_W1fam`, `ExpAvgGen_W1iii`, `ExpAvgGen_W1iiiOfLW` added). The probe is a
sole writable file of row c that is never merged (ticket `:103`, Amend 1 item 9): **the hub must not bring it into `main`** (O1).
No band file, no merged `Chain/*` file, no frozen signature in the diff.

## 2. Statements against the binding texts
Public defs (docstrings stripped, name map applied, whitespace-normalised text compare):
```
$ python3 -I defdiff.py docs/tickets/checks/T2502-amend-1-check.lean RBM3D/Chain/ExpAvgGen.lean
T2502_W1i -> ExpAvgGen_W1i : IDENTICAL
T2502_W1ii -> ExpAvgGen_W1ii : IDENTICAL
T2502_tM -> ExpAvgGen_tM : IDENTICAL
T2502_MB -> ExpAvgGen_MB : IDENTICAL
T2502_W1iii -> ExpAvgGen_W1iii : IDENTICAL
T2502_W1iv -> ExpAvgGen_W1iv : IDENTICAL
T2502_W1fam -> ExpAvgGen_W1fam : IDENTICAL
T2502_W1iiiOfLW -> ExpAvgGen_W1iiiOfLW : IDENTICAL
T2502_ImproveCoregL -> STImproveCoregL : IDENTICAL
```
Targets against the shapes (`Audit.lean:131-141`; `lake env lean Audit.lean`, error lines only):
```
example : T2502_W1fam d law Flow mk = ExpAvgGen_W1fam d law Flow mk := rfl                      -- ok
example : T2502_ImproveCoregL d law Flow mk T0 = STImproveCoregL d law Flow mk T0 := rfl        -- ok
example : T2502_W1iiiOfLW d law Flow mk T0 = ExpAvgGen_W1iiiOfLW d law Flow mk T0 := rfl        -- ok
example ... : T2502_W1iii C μ τ = ExpAvgGen_W1iii C μ τ := rfl ; (W1iv, W1ii) ⟨rfl, rfl⟩        -- ok
example (hFF : Step5CasesGen_FlowFacts d Flow mk T0) : T2502_Target16a d law Flow mk T0 := stImproveCoregL_of hFF      -- ok
example (hFF : Step5CasesGen_FlowFacts d Flow mk T0) : T2502_Target16b d law Flow mk T0 := stImproveExpAvergL_of hFF   -- ok
example : T2502_Target16a d law Flow mk T0 := stImproveCoregL_of        -- Audit.lean:140:46: error: Type mismatch
example : T2502_Target16b d law Flow mk T0 := stImproveExpAvergL_of     -- Audit.lean:141:46: error: Type mismatch
```
So 16a and 16b equal the binding shapes **under one extra premise** `hFF : Step5CasesGen_FlowFacts d Flow mk T0`
(`Chain/Step5CasesGen:140`: `∀ κ > 0, ∃ κm > 0, ∀ sz ε 𝔠 𝔡 z, Flow … → sz.Admissible 𝔠 𝔡 ∧ (∀ n, T0 < 1) ∧ (∀ n, κm ≤ Im m) ∧ η = (1-t) Im m`).
- Authorisation: the ticket's family-premise table row 3 (`T2502.md:49`) lists this premise for targets **15, 16**; Amend 1 item 2 changes rows 9, 14, 15
  only and item 8 keeps the rest. The binding shapes `T2502_Target16a/16b` (check Part 3) list rows 9 + 14 (and 15) only. The two binding sources
  disagree; folding row 3 into the shapes is a dispatcher decision (**needs dispatcher sign-off**). Same pattern as the merged row-a wrappers
  (`Step6KitGen:677, 716, 747, 795` take `hFF`).
- Use in the proof (`ExpAvgGen.lean:1371-1376`): `hadm.2.2.1` → `SizeTendsto` (needed for `hbig`, `:1387`, which absorbs `Cs (CM+1)` into `N^{τ/3}`,
  and for `st6_prec_det_iffg`); `hT0` → `u < 1`; `himm` → `κm ≤ Im m` (envelope, moments). `ExpAvgGen_W1fam` supplies none of these (`Flow` is an
  arbitrary predicate). Auditor reasoning, not compiled: without `SizeTendsto` the `≺` conclusion at a constant size sequence reads
  `|x_a| ≤ B²`, while the hypotheses give only `Cs (CM+1)`-multiples; so the premise is not removable in general.
- Discharges: band `step5CasesGen_flowFacts_band` (used in the instances, §3); BA `baStep5CasesGen_flowFacts` (U2-BA, merged; ticket row 3).
  No vacuity: it is a merged family text with both discharges.

16c `stExpAvgUgL_of_core` (Amend 1: "the 1b fixes its shape"): against `st6_expAvgU_of_ping` (`Step6KitGen:338-345`), read by `grep -A14`:
identical binder list and conclusion `STExpAvgUgL (mk sz z) (law sz) s t`, with `hAvg : STImproveExpAvergL …` replaced by `hCore : STImproveCoregL …`
and one added premise `hiii : ∀ u, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → ExpAvgGen_W1iii (mk sz z) (law sz) u` — exactly Amend 1 item 1 (16c).
Quantifier order: `Cs CM` after `(κ, ε, 𝔡)` and before `(𝔠, sz, z)` (inside the identical `ExpAvgGen_W1fam`); no `∃` after `(sz, z)`; W1 (iii) per time.

Targets 14, 15 (fixed-size Stein / sequence part) are private machinery feeding 16a (ticket `:40-41`: no pinned statement); judged through 16a.

C1/X1-C1 hypothesis rule over the public statements (§1 lines 51-121 and §8 lines 1360-1432):
```
$ sed -n '51,121p;1360,1432p' RBM3D/Chain/ExpAvgGen.lean | grep -nE '\bmE\b|zt E|zt \(|\|E\||2 - κ|etaT|lemT|STFlow|STflowE|STKloop|Lloop|loopFine|Ugen|uKer d|mSigma|seqHflow|seqP\b|withLam|lam0|BAflowLam0|norm_mE|Prec sz\b|ThetaN d|STthetaOp|HflowBlock|PF d' | wc -l
0
```
No hypothesis in a structure field (no new structure/class); no cycle (imports are merged modules; 16b ← 16a, 16c ← `STImproveCoregL` as a premise).

## 3. Compiled nonempty instances (all in `ExpAvgGen.lean` §10, compiled by the module build below)
Data: `d = 3`, `sz0` (`L 0 = 4`, `W 0 = 32`, `size 0 = 2097152`, `lam 0 = 1/64`; `Defs/Sizes:260-270`), `z0` with `Re = 1/2`, `(κ,ε,𝔠,𝔡) = (1/10,1/10,1/6,1/10)`
(`flow_z0`, `Induction/Defs:435`), `tInst ≡ 1/16`, `sInst ≡ 0` (`Induction/Defs:439-440`); `0 ≤ 1/16 ≤ lemT` by `sz0_ht`.
| endpoint | line | deterministic premises discharged | left as hypotheses |
|---|---|---|---|
| family texts (rows 9 + 14, iv) | `:1551` | all (`ExpAvgGen_band_W1fam 3 … flow_z0`) | none |
| 16a `stImproveCoregL_of` | `:1558` | `hFF` (`step5CasesGen_flowFacts_band 3`), W1fam (band), `3 ≤ 3`, positivity, `0 ≤ u ≤ T0` | `LWAvgLawgL`, `STLKgL`, `ExpAvgGen_W1iii` at `tInst` (per-time stochastic premises) |
| 16b `stImproveExpAvergL_of` | `:1565` | `hFF`, W1fam, row 15 (`ExpAvgGen_band_W1iiiOfLW 3`), the rest as 16a | `LWAvgLawgL`, `STLKgL` |
| 16c `stExpAvgUgL_of_core` | `:1571` | core = 16a at the band; `hK1` (`Step6KitGen_K1_band`), `sz0_tendsto`, `sInst < tInst ≤ lemT < 1`; `hiii` from row 15 + `LWAvgLawgL_of_STAvgUgL_at` | `STStep2CoregL`, `STLKUgL` (pins) |
| band pin through 16b | `:1583` | `STImproveExpAver 3 := stImproveExpAver_of_gL 3`, no hypothesis | none |
Nondegenerate: `N = 2097152`, nonempty lattice, `0 < u = 1/16 < 1`; no `False` premise. The 16a example keeps W1 (iii) open although row 15
gives it at the band; the 16b and 16c examples discharge it from `LWAvgLawgL` (acceptable: W1 (iii) is a per-time stochastic premise, Amend 1 item 2).

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Chain.ExpAvgGen 2>&1 | grep -E "error|sorry|Build completed"; grep -c "^warning: RBM3D/Chain/ExpAvgGen" build.out
✔ [3867/3867] Built RBM3D.Chain.ExpAvgGen (15s)
Build completed successfully (3867 jobs).
0
$ grep -nE "sorry|admit|native_decide|^\s*axiom " RBM3D/Chain/ExpAvgGen.lean | wc -l
0
$ lake env lean Audit.lean 2>&1 | grep "depends on axioms"
'RBM.BA.stImproveCoregL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stImproveExpAvergL_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stExpAvgUgL_of_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ExpAvgGen_band_W1fam' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ExpAvgGen_band_W1iiiOfLW' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.stImproveExpAver_of_gL' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build 2>&1 | grep -E "error|axiom audit|Build completed"     # full build incl. #assert_rbm_axioms with the registry edits
info: RBM3D.lean:620:0: axiom audit: 15216 theorems, 4706 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4390 jobs).
```
Registry (Amend 1 item 4, "the block is checked by the auditor"): `ExpAvgGen_W1fam`, `ExpAvgGen_W1iii` in `owedProps` with the owner text of
item 4 split over the two lines (V1-BA; TL1 `BATwistAvgLaw` via `TwistPins_circ_term`; probe `T2502c_ba_W1fam` 0f0ad532; public `CltFlowBA_MB_decay`);
`ExpAvgGen_W1iiiOfLW` in `owedProps` marked "band-only; BA: not produced". Accepted: all three are hypotheses of public theorems that no generic
theorem concludes; the full build passes.

## 5. Paper deltas
- Matrix `M`, W1 (iii)/(iv) premises, per-time form (16a) vs uniform form (16c): covered by **D727** (`docs/paper-deltas.md:1813`, from `T2502ca`);
  the prove report (d) 5 confirms the lines `6:10-21`.
- `hFF` (row 3: admissible sizes, `T0 < 1`, `Im m ≥ κm`): part of the paper's setting "of lem:main_ind" (`6:12-21`); not a paper delta, a ticket-shape
  question (§2).
- No other Lean/paper statement difference found.

## 6. Observations (no verdict effect)
- O1. The probe `RBM3D/Probe/T2502Pins.lean` is in `git diff main...t/T2502c`; it is a row-c writable file that is never merged. The hub's step (A)3
  must bring in only `RBM3D/Chain/ExpAvgGen.lean`, `RBM3D.lean`, `RBM3D/Test/Axioms.lean`.
- O2. `stImproveExpAver_of_gL` is a public, unpinned name without the stem `ExpAvgGen_` (§3 (E)); no clash on `main` (prove report (b) grep: the
  only hit is registry text). Naming only.
- O3. The prove report (a′) 3 / (d) 1 itself flags `hFF`; this audit confirms the type mismatch without it (§2) and leaves the decision to the dispatcher.

## 7. Verdict per target
| target | verdict |
|---|---|
| 14, 15 (private Stein / sequence machinery) | PASS (through 16a) |
| public defs (Amend 1 item 3, nine) | PASS — text-identical and `rfl` to the binding texts |
| 16a `stImproveCoregL_of` | PASS — **needs dispatcher sign-off**: equals `T2502_Target16a` only under the extra premise `hFF` (ticket table row 3, targets 15, 16) |
| 16b `stImproveExpAvergL_of` | PASS — **needs dispatcher sign-off**: same extra premise `hFF` against `T2502_Target16b` |
| 16c `stExpAvgUgL_of_core` | PASS |
| band discharges (`ExpAvgGen_band_W1fam`, `ExpAvgGen_band_W1iiiOfLW`, `stImproveExpAver_of_gL`), instances | PASS |
Overall T2502c: **PASS, needs dispatcher sign-off** (accept `hFF` in 16a/16b, i.e. read row 3 into `T2502_Target16a/16b`, or amend the shapes).
No repair list: dropping `hFF` would need premises that `ExpAvgGen_W1fam` does not supply (§2).
