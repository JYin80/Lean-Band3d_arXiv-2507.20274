Auditor model: claude-opus-5-5

# T2126 audit (round 1) — S1-30 `Green/GbEXP` — Sun Oct  4 10:54:36 UTC 2026

Audit worktree `RBM3D-wt/T2126-audit1`, detached at `298d757` (`t/T2126`, merge base `471b643`).

## 1. Scope, build, hygiene
```
$ git diff --name-only main...t/T2126
RBM3D/Green/GbEXP.lean
RBM3D/Test/Axioms.lean
$ git diff main...t/T2126 --stat -- RBM3D/Green/LocalLaw.lean RBM3D/Green/Pins.lean RBM3D/Induction/Defs.lean | wc -l
       0
$ git merge-tree --write-tree main t/T2126 | head -3
f77e87008d40f6ae76f34ef32ebbd2f075472f32          (no conflict)
$ lake build RBM3D.Green.GbEXP | tail -2     (audit worktree)
✔ [3359/3359] Built RBM3D.Green.GbEXP (4.5s)
Build completed successfully (3359 jobs).        exit=0
$ grep -n "GbEXP.lean" build.out             (warnings of the new file)
(none)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Green/GbEXP.lean
(none)
```

## 2. Statements and axioms (`lake env lean ax.lean`, exit 0)
```
@fixedTimeFAThm : ∀ {d : ℕ}, 1 ≤ d → FixedTimeFAThm d
@ibpDetThm : ∀ {d : ℕ}, 1 ≤ d → IBPDetThm d
@gbEXPV3 : ∀ {d : ℕ}, 3 ≤ d → GbEXPV3Theorem d
@stGbEXP_holds : ∀ {d : ℕ}, 3 ≤ d → RBM.Gauss.Sizes.STGbEXP d
@stStep1_holds : ∀ {d : ℕ}, 3 ≤ d → RBM.Gauss.Sizes.STStep1 d
'RBM.Green.fixedTimeFAThm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.ibpDetThm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.gbEXPV3' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stGbEXP_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stStep1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Against the ticket's pins: the conclusions are the merged, unchanged pins `FixedTimeFAThm d`
(`LocalLaw.lean:176`), `IBPDetThm d` (`:186`), `GbEXPV3Theorem d` (`Pins.lean:224`), `STGbEXP d`,
`STStep1 d` (`Induction/Defs.lean:329, 349`); the only added binders are `hd`, as the ticket
prescribes (item 1: weakest `hd`, `1 ≤ d`; items 2-3: `3 ≤ d`). `fixedTimeFAThm` uses `hd` only at
`Nat.le_self_pow (by omega)` (`W ≤ W^d`, `GbEXP.lean:536`); `ibpDetThm` passes `hd` to the merged
`perTimeDomAt_ibpRem` (D200). No `hd`-free general statement is lost: the pins at `d = 0` are
vacuous (`SizeTendsto` forces `1 ≤ d`, prove report (a′)).

Composition (merged signatures):
```
LocalLaw.lean:850  theorem LocalLaw_gbEXPV3Theorem_of_fa_ibp (hd : 3 ≤ d) (hFA : FixedTimeFAThm d) (hIBP : IBPDetThm d) : GbEXPV3Theorem d
Pins.lean:1152     theorem stGbEXP_of_v3 (h : GbEXPV3Theorem d) : STGbEXP d
Step1.lean:525     theorem step1TargetV3_holds (d : ℕ) : RBM.Ind.Step1TargetV3 d
GbEXP.lean:806     gbEXPV3 hd := LocalLaw_gbEXPV3Theorem_of_fa_ibp hd (fixedTimeFAThm (by omega)) (ibpDetThm (by omega))
GbEXP.lean:816     stStep1_holds hd := RBM.Ind.step1TargetV3_holds d (stGbEXPii_of_v3 (gbEXPV3 hd)) (stGbEXPij_of_v3 (gbEXPV3 hd))
```
No hypothesis beyond `hd` on any endpoint; no structure-field hypothesis introduced (the file
declares no `structure`); dependencies are merged files (imports: `Green/FlucThreshold`,
`Green/IBPRem`, `Green/LocalLaw`, `Induction/Step1`); no cycle (the module compiles).

Supporting declarations (item 4): RBM2D `c9a24cf` public names absent here (`comm -3`):
```
FlucAvgDet_check_* (5), FlucAvgDet_rangeCond_zero, GbEXP_check_* (5), IBPDet_check_* (3)   -- RBM2D Checks sections
IBPDet_hΨlow                                                                                -- replaced by merged IBPRem_hΨlow_of_floor (ticket)
new here: stGbEXP_holds, stStep1_holds
```
The floor premise of the ported `FlucAvgDet_family`, `_budgetFamily_absorb`, `_weighted` is
`W^{-d/2} ≤ Ψ` (the pins' floor); the `d = 2` premise `W⁻¹ ≤ Ψ` is not used anywhere (`grep` in prove
report b.7, and `gbEXP_W_inv_not_le_psi` shows it fails at the instance). Weights: row family
`boundedWeight_svarF` (`c = W^{-d}`, `#A = (2d+1)W^d`), block family `uniformWeight_blockAvg2 …
.toBoundedWeight` (`c = W^{-d}`, `#A = W^d`) — the bounded form of DECISIONS §30, as the ticket asks.

## 3. Compiled nonempty instances (all in `GbEXP.lean` §11; compiled by the build above)
Data: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), `Instance.premises`
(`κ = δ = 1/20`, `𝔠 = 1/6`, `𝔡 = 1/10`), `E = STflowE z0`, `tInst ≡ 1/16` (`Induction/Defs.lean:440`),
`Ψ = W^{-3/2}` (floor with equality), `a = 1/4`.
| endpoint | instance (line) | deterministic hypotheses | kept hypotheses |
|---|---|---|---|
| `fixedTimeFAThm` | `gbEXP_inst_fixedTimeFA` (895) | all discharged (`Admissible`, `|E|<2-κ`, `0≤t<1`, `RangeCond`, `a>0`, `Ψ≥0`, floor `le_rfl`, ceiling `gbEXPPsi_ceiling`) | `LocalLawDetSeq` (the pin's own random premise, output of merged `localLawDetThm`) |
| `fixedTimeFAThm` | `gbEXP_inst_fixedTimeFA_zero` (916), `t ≡ 0` | all | none |
| `ibpDetThm` | `gbEXP_inst_ibpDet` (906), `_zero` (927) | all | as above / none |
| `gbEXPV3` | `gbEXP_inst_gbEXPV3_ij_ii` (939) | all | none (`c > 0` free) |
| `gbEXPV3` (3rd clause) | `gbEXP_inst_gbEXPV3_avg` (950) | all | `AsGMcSeq`, `LoopDetSeq` (premises of the clause itself) |
| `stGbEXP_holds` | `gbEXP_inst_stGbEXP` (963) | all | none |
| `stStep1_holds` | `gbEXP_inst_stStep1` (972), `s ≡ 0 < t ≡ 1/16` | all (`STFlow`, ranges, `STConStInd`) | `STKbound`, `STLK`, `STLocalMax` (ST-6 gate pins) |
Nondegenerate: `N = 2097152`, `t = 1/16` (and complementing `t = 0` instances with no hypothesis),
no empty index, no `False` premise, `Ψ` at the floor (not an astronomically large witness).

## 4. Registry (`RBM3D/Test/Axioms.lean`) and root axiom audit
Diff removes `STStep1`, `GbEXPV3Theorem`, `FixedTimeFAThm`, `IBPDetThm` from `owedProps`
(`FlucGainUpTo'` line only re-terminated with `]`). Check at the branch state with the hub's merge
import (scratch `precheck.lean` = the 170 `import` lines of `RBM3D.lean` + `import RBM3D.Green.GbEXP` +
`#assert_rbm_axioms`; all root modules rebuilt in the audit worktree first):
```
$ lake build <170 root modules> RBM3D.Green.GbEXP | tail -1
Build completed successfully (3873 jobs).
$ lake env lean precheck.lean      (exit=0)
axiom audit: 3904 theorems, 1351 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 75 (borrowed 1, owed 59, structural 15).
registry: 5 borrowed + 96 owed + 39 structural; 65 registered premise(s) carry nothing yet: [...]
```
None of the four removed names is reported as an unregistered premise, so the removal is right and
no "proved for 3 ≤ d" comment is needed. Without the root import the full build fails (prove report
b.1: `[RBM.Green.IBPDetThm, RBM.Green.FixedTimeFAThm]`); the hub adds the import at merge
(CLAUDE.md §3 (A) 4), so this is expected. The hub's full build at merge is on `main` (`6329018`),
which the merge-tree above shows merges cleanly.

## 5. Paper deltas
Lean/paper differences and their coverage (prove report (d).5):
- floor `W^{-d/2} ≤ Ψ` with `W^d ≤ N` in place of RBM2D `W⁻¹ ≤ Ψ`, `W ≤ size` → `T2126a`;
- `BoundedWeight` row/block families (`c = W^{-d}`, `#A = (2d+1)W^d`, `W^d`), `jasdu` form → `T2126b`;
- `hd : 1 ≤ d` / `3 ≤ d` binders on the endpoints → `T2126c`.
The pins themselves are merged and unchanged (their deltas belong to T2108/T2123). Coverage complete.

## 6. Observations (no effect on verdict)
- O1. Instance data differ from preflight (a)(ii) (`E ≡ 0`, `t = 1/2`) — the prover says so (b.11.7)
  and redid the limit check at the Lean data (b.10, `W = 1..4`, small sizes; the external
  `LocalLawDetSeq` is not derived, as allowed).
- O2. `FlucAvgDet_perTime_reindex` and `IBPDet_norm_condExpDiag_sub_le_two_phi` have no standalone
  instance; they are supporting lemmas exercised inside the endpoint instances (not endpoints).

## Verdict per target
| target | statement | vacuity / hidden hyp / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `fixedTimeFAThm (hd : 1 ≤ d)` | = pin | none | yes | ok | T2126a-c | **PASS** |
| `ibpDetThm (hd : 1 ≤ d)` | = pin | none | yes | ok | T2126a, c | **PASS** |
| `gbEXPV3 (hd : 3 ≤ d)` | = pin | none | yes | ok | T2126c | **PASS** |
| `stGbEXP_holds (hd : 3 ≤ d)` | = ticket | none | yes | ok | T2126c | **PASS** |
| `stStep1_holds (hd : 3 ≤ d)` | = ticket | none | yes | ok | T2126c | **PASS** |
| registry (`Test/Axioms.lean`) | 4 lines removed | — | — | root audit exit 0 with import | — | **PASS** |

**Ticket verdict: PASS.** No dispatcher sign-off needed. Hub: add `import RBM3D.Green.GbEXP` after the
last `import` line of `RBM3D.lean` at merge.
