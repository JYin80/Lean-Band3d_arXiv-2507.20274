Auditor model: claude-opus-5-5

# T2386 audit (round 1) — BA-T T8, the Step 2 vocabulary over the carrier

`date -u`: Sat Oct 10 16:25:58 UTC 2026. Branch `t/T2386` = `3297200`, base `61849a6`. Audit worktree `RBM3D-wt/T2386-audit1`
(detached at `3297200`); G1 base worktree `RBM3D-wt/T2386-audit1-base` (detached at `61849a6`). Scripts in
`scratchpad/T2386/audit/` (`cmp.py`, `g1.lean`, `g1cmp.py`, `cover.py`, `ax.lean`). Inputs: ticket, Amend 1, check file, prove report.
**Verdict: PASS** (all targets 1–7). No dispatcher sign-off needed.

## 1. Diff scope, Step2Defs untouched, stop line

```
$ git diff --stat main...t/T2386
 RBM3D.lean | 1 + ; RBM3D/BA/FlowPins.lean | 44 +- ; RBM3D/Chain/Carrier.lean | 13 +- ; RBM3D/Chain/Step2Gen.lean | 986 +++
 RBM3D/Induction/LocalAvg1.lean | 287 ; RBM3D/Induction/LocalAvg2.lean | 331 ; RBM3D/Test/Axioms.lean | 7 +
 7 files changed, 1493 insertions(+), 176 deletions(-)
$ git diff main...t/T2386 -- RBM3D/Induction/Step2Defs.lean | wc -l
       0
$ git diff main...t/T2386 -- '*.lean' | grep '^+' | grep -nwE 'sorry|admit|native_decide|axiom'; echo $?
1   (no hit)
```
All 7 files are sole writable files. Net stop-line reading: 986 + (215−72) + (258−73) + (14−30) + (12−1) + 7 + 1 = **1317 ≤ 1500**.
Imports added: `Chain/Step2Gen` imports `Chain.Carrier`, `Induction.Step2Defs` only; `LocalAvg1` and `FlowPins` gain
`import RBM3D.Chain.Step2Gen`. No cycle (Lean accepts the import graph; build below).

## 2. Build and axioms (audit worktree)
```
$ lake build RBM3D.Chain.Step2Gen RBM3D.Induction.LocalAvg2 RBM3D.BA.FlowPins RBM3D.Test.Axioms   -> exit 0
Build completed successfully (3808 jobs).          (grep -c '^error' build.log: 0; warnings in edited files: long lines, unused names only)
$ lake build        (whole library: #assert_rbm_axioms + registry scan)  -> exit 0
premises found by scanning: 119 (borrowed 1, owed 53, structural 46, refuted 6, superseded 13).
Build completed successfully (4200 jobs).
$ lake env lean ax.lean     (collectAxioms over every constant of Step2Gen, LocalAvg1, LocalAvg2, plus bandFM, BAStep2)
constants checked (Step2Gen, LocalAvg1, LocalAvg2, bandFM, BAStep2; incl. private): 199; with a non-standard axiom: #[]
'RBM.BA.bandStep2Data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.bandFM_STGijGEX' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stInitialGT2_of_L2decayG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep2AvgPT_of_L2decayG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep2LocalPT_of_L2decayG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stLocalAvgOfL2_holdsG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stLocalAvgOfL2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stStep2LocalPT_of_L2decay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAStep2' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean docs/tickets/checks/T2386-check.lean     (on the branch)  -> exit 0, 0 error lines
```

## 3. G1 (target 1 and target 5): frozen statements unchanged
`g1.lean` prints, with `pp.all`, the type of every public constant of `LocalAvg1/2`, of `bandFM`, `STJhatg`, `STLWassmExpgL`
and every `bandFM_*` of `FlowPins` (and the body hash of the three moved defs); run on base `61849a6` and on the branch:
```
$ python3 -I g1cmp.py g1-base.txt g1-branch.txt
base decls: 36  branch decls (same filter): 47
identical type (pp.all; defs also body hash): 36
DIFFERENT: []
MISSING on branch: []
names: STJhatg STLWassmExpgL bandFM bandFM_STDecay bandFM_STDecayStrong bandFM_STEEk bandFM_STExp2 bandFM_STInitialGT2 bandFM_STKbound
 bandFM_STLK bandFM_STLWassmExp bandFM_STLmax bandFM_STLocalEntry bandFM_STLocalMax bandFM_STStep1Loop bandFM_STStep1Weak eq_1
 localAvg1_STWB_comp localAvg1_STWB_ge localAvg1_STWB_le localAvg1_data localAvg1_det localAvg1_domAt_of_le_const
 localAvg1_maxLoop2_le localAvg1_perTime_of_stoch localAvg1_rpow_half_sq localAvg1_stochDomAt_of_whp localAvg1_whp_L2
 localAvg1_whp_omega localAvg2_entry_le localAvg2_rhs_le stInitialGT2_of_L2decay stLocalAvgOfL2_holds stLocalPsi
 stStep2AvgPT_of_L2decay stStep2LocalPT_of_L2decay
```
So `bandFM` moved with identical type and body (`Carrier.lean:180`), `STJhatg`/`STLWassmExpgL` moved with identical type and body
(Amend 1 item 6), and all 19 `LocalAvg` publics keep name and statement (pp.all equal; stronger than `example : <old> := <name>`).

## 4. Target 2 (c): the probe's Step 2 family and target 4 (`BAStep2`) against the pin

Bodies extracted by script from `t/T2379:RBM3D/Probe/T2379Pins.lean:39-104` and from the branch (`Step2Gen.lean`, `FlowPins.lean`),
docstrings stripped, whitespace normalised:
```
$ python3 -I cmp.py probe.lean Step2Gen.lean FlowPins.lean
STAvgUgL body identical          STLocalEntryUgL body identical      STGdecayWgL body identical
STStep2ConclgL body identical    STStep2G body identical             STStep2_iff body identical
BAStep2 body identical           bandFM_STAvgU body identical        bandFM_STLocalEntryU body identical
bandFM_STGdecayW body identical  bandFM_STStep2Concl body identical
```
`STStep2G` binder order (section variables) is `d, law, Flow, mk, T0`, as in the probe. `BAStep2` is a `Prop` def with no proof
(`FlowPins.lean:432`), quantifier order and hypotheses those of `STStep2G` (`3 ≤ d → ∀ κ ε 𝔡 > 0, ∃ Cd 𝔠d, ∀ 𝔠 sz z, Flow → ∀ s t …`).

## 5. Target 2 (b), (d): vocabulary coverage and bridge kinds

```
$ python3 -I cover.py RBM3D-wt/T2386-audit1
Step2Defs public defs: 59
no generic g/gL form: ['STprof', 'STEEk', 'STPsiClass', 'STContractPt', 'STStep2', 'STScaleOk', 'STScaleAdm', 'Ψ0']
generic form but no bridge naming both: ['STInitialGT2', 'STLWassmExp']
bridge proof kinds: {'rfl': 28, 'Iff.rfl': 30, 'by': 1} non-rfl: [['bandFM_STGijGEX']]
```
Resolution of the residue (by reading): `STEEk` → `STEEg` (Carrier) with bridge `bandFM_STEEk` (FlowPins, G1 list); `STStep2` →
`STStep2G` via `STStep2_iff`; `STInitialGT2`, `STLWassmExp` bridges are `bandFM_STInitialGT2`, `bandFM_STLWassmExp` in `FlowPins`
(G1 list); `Ψ0` is an instance def at `sz0` (`Step2Defs.lean:982`); `STprof`, `STPsiClass`, `STScaleOk`, `STScaleAdm` read only
`sz`; `STContractPt` quantifies over an arbitrary Hermitian `H` and `z` (`Step2Defs.lean:391-400`), no band object. All 16 names of
Amend 1 (`STGMM`, `STNewKLKAt`, `STNewKLK`, `STK2decay`, the N-loop 12) have a generic form and an `rfl`/`Iff.rfl` bridge at
`bandStep2Mat` (`Step2Gen.lean:828-851, 889-892`); the energy pins read `mk sz (fun _ => E)` as Amend 1 item 2 asks. None deferred.
The single proved bridge `bandFM_STGijGEX` (`Step2Gen.lean:594-601`) is an `↔` proved by `simp [FlowFM.GM, bandFM, p.2]`
using `x ≠ y` and diagonal band `M`: a genuine equivalence, not a one-way adapter.

## 6. Target 3: the generic `LocalAvg1/2` statements

| generic (file:line) | facts as arguments | band corollary proved from it |
|---|---|---|
| `stInitialGT2_of_L2decayG` (LA1:379) | `hdat` (size data), `hweak`, `hL2` | `stInitialGT2_of_L2decay` (`exact …G (bandStep2Data sz z) sz.seqP …`) |
| `stStep2AvgPT_of_L2decayG` (LA1:468) | `hdat`, `hGav : STGavLGEXgL` ∀ `u ≤ T0`, `hweak`, `hL2` | `stStep2AvgPT_of_L2decay` |
| `stStep2LocalPT_of_L2decayG` (LA2:367) | `hdat`, `hGii`, `hGij` (GM form), `hweak`, `hL2` | `stStep2LocalPT_of_L2decay` (LA2:446-458; `hGij` via `bandFM_STGijGEX`) |
| `stLocalAvgOfL2_holdsG` (LA2:467) | `hF : Flow → flowOK`, `hdat`, `hGii`, `hGij`, `hGav` (∀-flow) | `stLocalAvgOfL2_holds` (LA2:496-508) |
| helpers `localAvg1_whp_L2G/_whp_omegaG/_maxLoop2_leG`, `localAvg2_rhs_leG/_entry_leG` | `hswap` (L_swap) | old helpers at `bandFM sz E` |

The generic theorems need `0 < d` only; `3 ≤ d` stays on the band corollaries, where it discharges `stGbEXP_holds` (G1 equal above).
`hdat` has the band quantifier shape (`∃ cB c > 0, ∀ t ≤ T0, ∀ᶠ n, ∀ u ≤ t n, …`) and the band corollaries discharge it with
`localAvg1_data` (from `ST_Bdata_holds`). No generic `Step2Iterate` added (T1).

## 7. Hidden hypotheses, vacuity, cycles

- `Step2Data` fields that are facts: `flowOK_adm`, `flowOK_T` (`0 < κ → flowOK → T0 n < 1`), `L_swap` (trace cyclicity), as the
  ticket's "base facts" design asks. All three are discharged at the band by `bandStep2Data` (`Step2Gen.lean:138-144`: `h.1`,
  `lemT_lt_one (Step2Gen_flow_im_pos h n)`, `Step2Gen_loopFine_swap` = `Matrix.trace_mul_comm`), so the structure is inhabited at
  nondegenerate data; at BA they are T8-BA's obligations (not claimed here).
- `Step2Mat` holds data only (`LM`, `GMM`, `LIM`, `KI`, `Pp`, `Hpath`), each filled at the band by the merged band object.
- External/other-gate inputs (`STStep1WeakgL`, `STL2decayPTgL`, `STGiiGEXgL`, `STGijGEXgL`, `STGavLGEXgL`) are explicit
  hypotheses, registered as owed with owners (`Test/Axioms.lean` +5 lines); at the band each is either discharged
  (`stGbEXP_holds`) or is the band pin itself (`STStep1Weak`, `STL2decayPT`). `BAStep2` is assumed by no theorem: no owed line
  needed; the full-build registry scan passes. No dependency on unmerged code (the imports are `main` modules).

## 8. Compiled nonempty instances (d = 3, `sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`; `z0`; `s ≡ 0`, `t ≡ 1/16`, `u ≡ 1/32`)

- `Step2Gen.lean:904-986`: 8 examples apply every bridge at `bandStep2Mat sz0 (STflowE z0)` / `bandFM sz0 (STflowE z0)` /
  `d = 3`; the first proves `(bandStep2Data sz0 z0).flowOK (1/10) (1/10) (1/6) (1/10)`, `T0 n < 1`, and `L_swap` at `ω`.
- `LocalAvg1.lean:563-575`, `LocalAvg2.lean:554-583`: each of the four endpoint generic theorems applied at `bandStep2Data sz0 z0`,
  law `seqP sz0`, window `[0, 1/16]`; `hdat` discharged (`localAvg1_inst_hdat`), `hGii/hGij/hGav` discharged by
  `stGbEXP_holds (3 ≤ 3)`; only `STStep1WeakgL`, `STL2decayPTgL` (other gates' pins) remain hypotheses.
- Helpers: `localAvg1_whp_L2G/_whp_omegaG/_maxLoop2_leG`, `localAvg2_rhs_leG` fully discharged at `n = 0`, `u = 1/32`.
- `FlowPins.lean:1430`: `example : BAStep2 3 = STStep2G 3 … := rfl`.
All compile in the module builds of §2. No `N = 0`, empty index, collapsed window or `False` premise.

## 9. Paper deltas
The only Lean/paper statement difference is `STGijGEXgL` stated for `(G_t − M)_{xy}`, `x ≠ y`, versus the paper's `(G_t)_{xy}`
(`(GijGEX)`, `3_5:24`); proposed as **T2386a** in the prove report §(d) (Amend 1 item 8), equal at the band by `bandFM_STGijGEX`.
Every other generic form equals its band statement by `rfl`/`Iff.rfl` at the band carrier; the band statements are unchanged (§3).

## 10. Observations (no RETURN)

- O1. `localAvg2_entry_leG`'s example keeps `hΩ`, `hij`, `hii` (per-sample event inequalities, the outputs of `lem_GbEXP` and the
  weak law at `ω`) as hypotheses. It is a helper, not an endpoint; the endpoint `stStep2LocalPT_of_L2decayG` discharges them.
- O2. `Test/Axioms.lean` also registers `RBM.BA.Step2Data.flowOK` under `structuralProps` and an owed line for `STStep1WeakgL`
  (not named in Amend 1 item 7); both were required by the registry scan (prove report (a′) addendum), and the full build passes.
- O3. Merge note for the hub: `git merge-tree main t/T2386` reports a content conflict in `RBM3D.lean` only (main gained 3 import
  lines since `61849a6`); it is the one-line union of H23 (b). `Test/Axioms.lean` auto-merges.
- O4. `Step2Mat.LM/GMM/LIM/KI` are independent of the `FlowFM` fields `L/G/M/K` (no consistency fact such as `STLM_seqHflow`);
  that link belongs to T1/T7/T8-BA, as the ticket defers.
