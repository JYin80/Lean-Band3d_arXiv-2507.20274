Auditor model: claude-opus-5-5
# T2187 audit (round 1) — UN-01b `RBM3D/Universality/PinsK.lean`
Time: Mon Oct  5 14:47:00 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2187-audit1`, detached at `c167e00` (t/T2187); main = merge base = `f23811b`. Scratch: `scratchpad/T2187/` (`ext.py`, `d1.py`, `d2.py`, `ax.lean`, `precheck.lean`).

## 1. Scope, build, axioms
```
$ git diff --stat main...t/T2187
 RBM3D/Test/Axioms.lean        |  18 +
 RBM3D/Universality/PinsK.lean | 752 ++++++++++++++++++++++++++++++++++++++++++
$ lake build RBM3D.Universality.PinsK        (audit worktree)
Build completed successfully (3329 jobs).   exit=0
$ lake build RBM3D                           (audit worktree, root; root does not import PinsK yet)
Build completed successfully (3990 jobs).   exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Universality/PinsK.lean ; echo grep-exit=$?
grep-exit=1
$ (ax.lean: `#print axioms` of all 68 public `theorem`/`def`/`structure` names of PinsK) lake env lean ax.lean
exit=0   lines "depends on axioms: [propext, Classical.choice, Quot.sound]": 68   other lines: 0
$ precheck.lean = import RBM3D / import RBM3D.Universality.PinsK / #assert_rbm_axioms ; lake env lean precheck.lean
axiom audit: 5445 theorems, 1945 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...
premises found by scanning: 109 (borrowed 1, owed 85, structural 23).
  RBM.Univ.UNClaim417C: 1  UNGreenCorrC: 1  UNGreenCorrAllC: 1  UNTrLocalInit: 1  UNStep1GoodC: 0  UNCoreC: 1
  UNOUQUEk: 1  UNOUDiagk: 1  UNEMCTE2k: 1  UNJakk: 1  UNUywk: 1  UNQuek: 2  UNLocAvgk: 1
  UNOURowk: 6  UNEMCTE2Rowk: 6  UNJakUywRowk: 6  UNClaimRowk: 6
exit=0
```
`Axioms.lean` diff: 17 `owedProps` lines (exactly the ticket's list, comment `(T2187, UN-01b: owed)`) + 1 `structuralProps` line `RBM.Univ.UNKind.bulk`; nothing else changed. Frozen files (`Pins.lean`, `OU.lean`, `EigenMeasurable.lean`, `GUEInvariance.lean`, `Step1Cond.lean`) not in the diff. Imports: `import RBM3D.Universality.Pins` only.

## 2. Statements against the pins (script diffs, run by the auditor)
`ext.py` cuts each declaration from its header to the first blank line / next command, drops field docstrings, normalises whitespace; theorems compared up to the top-level `:=` unless marked "(with proof)".
```
$ python3 d1.py      # check file docs/tickets/checks/T2187-check.lean lines 121-342 (section 2) vs PinsK
EMPTY UNModelC  EMPTY UNKind  EMPTY ouMatC  EMPTY ouInit  EMPTY UNClaim417C  EMPTY UNClaimAllC
EMPTY UNTrLocalInit  EMPTY UNOUQUEk  EMPTY UNOUDiagk  EMPTY UNEMCTE2k  EMPTY UNJakk  EMPTY UNUywk
EMPTY UNQuek  EMPTY UNLocAvgk  EMPTY UNOUClaimsk  EMPTY UNOURowk  EMPTY UNEMCTE2Rowk  EMPTY UNJakUywRowk
EMPTY UNClaimRowk
$ python3 d2.py      # probe a543154 and merged Pins.lean (main) under the auditor's own S1-S6 regexes
EMPTY probe UNKind
DIFF  probe UNKind.band   ['- ((UNModel.band', '+ (UNModel.band', '- sz).toC).toC', '+ sz).toC']
EMPTY probe UNOUQUEk / UNOUDiagk / UNEMCTE2k / UNJakk / UNUywk / UNQuek / UNLocAvgk / UNOUClaimsk
EMPTY probe UNOURowk / UNEMCTE2Rowk / UNJakUywRowk / UNClaimRowk
EMPTY probe un_claimAll_of_rowsk (with proof)
EMPTY probe ouInit, ouInit_isHermitian (with proof), vOUC, UNTrLocalInit, UNStep1GoodC, UNCoreC
EMPTY probe ouP_cylinder (with proof), UNOUQUEk_zero_of_UNQuek (with proof), inWindow_nonempty (with proof)
EMPTY probe ouMat->ouMatC, ouMat_isHermitian->ouMatC_isHermitian, ouMat_zero->ouMatC_zero,
      ouMat_eq_ouInit_add->ouMatC_eq_ouInit_add
EMPTY merged UNClaim417->UNClaim417C, UNClaimAll->UNClaimAllC, UNGreenCorr->UNGreenCorrC,
      UNGreenCorrAll->UNGreenCorrAllC, UNInfty1->UNInfty1C, UNUnivMain->UNUnivMainC
```
(Output lines grouped for length; each name printed its own EMPTY line.) The one DIFF is an artefact of the audit script: its two S6 regexes both fire on the probe's `M := UNModel.band` (giving `((UNModel.band sz).toC).toC`); the file has `M := fun sz => (UNModel.band sz).toC`, which is the ticket's text for `UNKind.band` verbatim.

Ticket-text statements checked by reading the file (`PinsK.lean` line):
- `UNModel.toC` `:61` = ticket text; `ouMatC_zero` `:85` `ouMatC M n 0 ω = M.H n ω.1`; `ouMatC_eq_ouMat_add` `:100` and the `example` `:133` carry `T2187_ouMatC_eq_ouMat_add` verbatim; `:138` carries `T2187_ouMatC_mean_zero`; `:469` carries `T2187_un_claimAll_of_rowsk`.
- `ouMatC_toC` `:119` is function equality `ouMatC M.toC = ouMat M`; `ouInit_toC` `:124` `= Real.exp (-t / 2) • M.H n ω`.
- `_toC` bridges `:174-247` are `↔` with the merged pins at `M`; `UNGreenCorrAllC.toAll` `:251` one direction via `toC`.
- band bridges `:522-578`: `UNOURowk_band` is `UNOURowk (fun d => UNKind.band d) (∀ d, UNMLOut d) UNLocAvgBand UNQueBand ↔ UNOURow` as pinned; the others `↔` the merged rows/pins.
- `un_claimAll_of_rowsk_band` `:580` concludes the merged `UNClaimAll sz (UNModel.band sz) E` from `|E| ≤ 2 - κ`.
Quantifier order, losses (`-c' + Cn * τU`, `𝔠 * 𝔡 / 30`, `𝔡 / 3`, `𝔡 / 6`), ranges and `Admissible` premises are the source's: the diffs are empty.

## 3. Hidden hypotheses, vacuity, cycles
- `UNModelC` adds data `mean` and the proof field `mean_herm` (a well-formedness field, discharged at construction: `toC` by `Matrix.isHermitian_zero`, `unPinsK_baC` `:717` by `PsiI_isHermitian`). No result-carrying field.
- `UNKind` fields are data; `bulk` is a Prop-valued predicate on `(sz, κ, E, n)` used as an explicit premise `∀ᶠ n, (K d).bulk sz κ E n` of the generic pins; at the band kind it is `|E| ≤ 2 - κ` (`unPinsK_band_bulk`, `rfl`), discharged at `E = 0`, `κ = 1/10` in the instances. Flow and initial matrix are not fields of `UNKind` (as the ticket requires): `ouMatC`, `ouInit` are functions of `M.mean`.
- Non-vacuity of the mean: `inst_ouMatC_ne_ouMat` `:728` builds a `UNModelC sz0` with mean `λΨ` and proves `ouMatC ≠ ouMat` at an entry, `n = 0`, any `t > 0`.
- No cycle: PinsK imports only `Pins.lean`; every dependency is merged (`Pins.lean`, Mathlib). Pins `UNCoreC`, `UNClaimAllC`, rows etc. are definitions (Props), registered owed; no theorem assumes its own conclusion.
- External hypothesis `UNL32` (borrowed, merged) is only passed through (`inst_bUniv_band_k`, `inst_coreC_band`); its limit check is in the prove report (a)(i)/(ii) (script output, `N = 2^21, τ = 1/2` and along `sz0`), unchanged from T2174.

## 4. Compiled nonempty instances (namespace `RBM.Univ.UNKInst`, all built, axioms as §1)
| instance | data | deterministic hypotheses discharged | kept (other gates' pins) |
|---|---|---|---|
| `inst_claimAllC_band` `:630` | `sz0`, `(1/6,1/10)`, `κ=1/10`, `E=0` | `3 ≤ 3`, `sz0_adm`, `0<1/10`, eventual bulk `|0| ≤ 2-1/10` | 4 generic band rows, `UNMLOut`, `UNLocAvgBand`, `UNQueBand` |
| `inst_claimAll_band_k` `:640` | same | same (via `un_claimAll_of_rowsk_band`) | same |
| `inst_bUniv_band_k` `:653` | `sz0`, `k=1`, `bump`, `E=0` | inside `UNInst.inst_bUniv_band` (merged) | merged rows, `UNL32`, `UNGUELocal`, `UNGreenCorrAll`, generic rows |
| `inst_coreC_band` `:673` | `(UNModel.band sz0).toC`, `msc`, `E=0`, `ρ=rhoSC 0`, `δ=1/2`, `E'=0`, `k=1`, `bump` | `sz0_adm`, `un_dens_msc_zero`, `|0|<2`, `1 ≤ 1`, `bump_testFun` | `UNCoreC`, `UNL32`, `UNGUELocal`, `UNGreenCorrAllC`, `UNTrLocal`, `UNTrLocalInit`, norm bound, `UNClaimAllC` (ticket list) |
| `inst_OUQUEk_zero_band` `:684` | `sz0`, `κ=1/10`, `τQ=1/2` | `3 ≤ 3`, `sz0_adm`, `0<1/10`, `0<1/2` | `UNQueBand` |
| `inWindow_nonempty` `:608` | any `sz : Sizes 3`, `z = E + i/N` | proved outright (`0 ≤ C₀`, `0 ≤ τU`) | none |
| `inst_ouMatC_ne_ouMat` `:728` | `sz0`, `n=0`, mean `λΨ`, entry blocks `0`/`e₁` | proved outright (`decide` on `blk`/`ofs`/`Adj`, no `native_decide`) | none |
`sz0` at `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152` (not degenerate, not astronomically large). Each instance listed in the ticket is present and has the ticket's form. The bridges are unconditional `↔`/`=` statements (no deterministic hypothesis) and are exercised by the instances (`UNClaimRowk_band` … `UNOURowk_band` in `inst_bUniv_band_k`; `UNClaimAllC_toC` in `inst_claimAll_band_k`; `UNQuek_band` in `inst_OUQUEk_zero_band`).

## 5. Name clashes
```
$ for n in <base names of every PinsK theorem/def/structure>; git grep -wn "$n" main -- 'RBM3D/*.lean' RBM3D.lean ':!RBM3D/Probe' | grep -E "(def|theorem|lemma|structure|abbrev) ([A-Za-z.]*\.)?$n\b"
band: 1 decl hits        (= merged `UNModel.band`; the new name is `UNKind.band`, a different declaration)
```
Unpinned public helpers carry the `unPinsK_` stem (`unPinsK_toC_toUNModel`, `unPinsK_band_bulk`, `unPinsK_band_M`); the rest are `private` (§3 (E)).

## 6. Paper deltas
- T2187a (proposed in the report): `UNModelC`/`ouMatC`/`…C` copies replace the probe's in-place amendment of `UNModel`/`ouMat`; Lean structure only. Covers every difference found in §2 (none after S1-S6).
- The centred flow itself and `UNCoreC`'s extra `UNTrLocalInit` premise come verbatim from the T2173 probe; the flow is D445 (T2173c) in `docs/paper-deltas.md:1404`; the two local laws are T2173 design item 4 (`docs/reports/T2173-prove.md:252`; `grep -c UNTrLocalInit docs/paper-deltas.md` = 0, so no separate entry: it is a Lean split of Step 1's input, observation only). No new uncovered statement difference.
- T2187b (registry class of `UNKind.bulk`, see §7).

## 7. Observations (no RETURN)
1. `RBM.Univ.UNKind.bulk` registered **structural**, while the ticket says "by §20's rule (unsure: owed)". DECISIONS §20 classes a Prop that describes a condition on data and is used as a hypothesis as structural; `bulk` is the energy set of a model class (`|E| ≤ 2 - κ` at the band kind), not a result. I agree with structural; the prover raised it as T2187b for the dispatcher to confirm. Changes no statement, instance, build or axiom.
2. `UNStep1GoodC` is carried by 0 theorems (pre-check), like merged `UNStep1Good`; expected, its consumers are later tickets.
3. `UNCoreC`'s premise `UNTrLocalInit` (inherited verbatim from the T2173 probe, not introduced here) has no own paper-deltas entry; the dispatcher may fold it into D445 or T2187a when numbering. Not a T2187 statement difference (§2 diffs empty).
4. Not targets (as the ticket says): band bridges for `vOUC`/`UNStep1GoodC`/`UNCoreC`, rows decomposing `UNCoreC`, BA-specific items. None present in the file.

## Verdict per target
| target | verdict |
|---|---|
| 1 vocabulary, flow, `toC` bridges | PASS |
| 2 claim-level copies, `UNTrLocalInit`, `vOUC`, `UNStep1GoodC`, `UNCoreC`, `_toC` bridges, `toAll` | PASS |
| 3 `UNKind`, `UNKind.band`, generic pins/rows, `un_claimAll_of_rowsk`, `ouP_cylinder`, `UNOUQUEk_zero_of_UNQuek` | PASS |
| 4 band bridges, `un_claimAll_of_rowsk_band` | PASS |
| instances (§4) | PASS |
**Overall: PASS.** No dispatcher sign-off needed for the merge (T2187b is a confirmation of a registry class, recorded in §7).
