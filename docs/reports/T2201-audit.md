Auditor model: claude-opus-5-5
# T2201 audit (round 2) — UN-01c `Universality/PinsDens` + `Test/Axioms.lean` registry

Written Mon Oct  5 19:01:59 UTC 2026 (`date -u`). `t/T2201` at `b818bb5` (repair of round-1 RETURN on top of
`b33918f`); merge base `3429d7d`; `main` now `cef761a` (adds only `Induction/NQEndLin.lean` + one root import; no
file of this ticket). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2201-audit2` (detached). Scratch files in the
session scratchpad `T2201/` (`Cmp2.lean`, `Reg.lean`, `Neg.lean`), never in the repository.

**Verdict: PASS** (all targets). Round-1 defect (missing compiled instances of `not_UNStep1GoodC`,
`unTrLocalInit_shift`, `unDensBandRow'_of_row`) is repaired; nothing else changed.

## 1. Files touched
```
$ git diff --stat main...t/T2201
 RBM3D/Test/Axioms.lean           |  53 ++-
 RBM3D/Universality/PinsDens.lean | 702 +++++++++++++++++++++++++++++++++++++++
$ git diff --stat b33918f t/T2201          # the repair
 RBM3D/Universality/PinsDens.lean | 20 ++++++++++++++++++++
```
Exactly the two sole writable files. The repair adds three `example`s (lines 680, 688, 694) in `RBM.Univ.UNDensInst`
and nothing else. `Axioms.lean` diff (`git diff main...t/T2201 -- RBM3D/Test/Axioms.lean`, read in full): 4 owed
lines (`UNStep1Good`, `UNInfty1Row`, `UNStep1GoodC`, `UNCoreC`) out; 4 primed owed lines with the ticket's comment
in; `UNDens'` appended to `structuralProps`; `def refutedProps` (4 names, evidence + successor per line) with
docstring; `classified` includes `refutedProps` in both `#assert_rbm_axioms` and `#assert_rbm_audit_detects`; the
disjointness check (`revived`); `refuted` counts in the registry and scan lines; one module-docstring paragraph.
`interfaceProps`, `certificates`, `scanPremises` unchanged. No merged signature touched.

## 2. Statements against the pin (script)
`Cmp2.lean` = `import RBM3D` + `import RBM3D.Universality.PinsDens` + check file `T2201-check.lean` lines 136-399
(sections 2-3 verbatim) + a meta command: rename constants `RBM.Univ.T2201Check.Y ↦ RBM.Univ.Y`, level params ↦ 0,
compare the check value with the library value (defs) / type (theorems): first `Expr.eqv` (alpha-equivalence),
else `withReducible isDefEq` (differences are only auxiliary proof constants, e.g. `unDensShift._proof_1` vs
`Nat.instAtLeastTwoHAddOfNat`, located by a first-difference walker). `#cmpsub` maps `UNDens' UNInfty1Row' UNCore'
UNCoreC' un_dens'_msc_zero` to the unprimed merged names and compares with the merged source.
```
$ lake env lean $S/Cmp2.lean ; echo exit $?          # exit 0
CMP UNDens' unDensShift UNStep1Good' UNInfty1Row' UNCore' UNDensBandRow' UNStep1GoodC' UNCoreC': IDENTICAL(syntactic)
CMP UNDens'.toUNDens unDens'_msc_of_unDens unDensBandRow'_of_row un_core_of_rows' un_bUniv_of_rows'
    unDensShift_of_le not_unDens'_unDensShift not_UNStep1Good not_UNStep1GoodC
    UNDensInst.not_UNStep1Good_band: IDENTICAL(syntactic)
CMP unDens'_freeConvST unDens_shift unTrLocal_shift unTrLocalInit_shift un_msc_box_zero un_dens'_msc_zero
    UNDensInst.{inst_core_band', inst_core_of_rows', inst_bUniv_band', inst_bUniv_band_k', inst_coreC_band',
    inst_dens'_uI, inst_T2190a_family}: IDENTICAL(up to proof terms, reducible defeq)
SUB UNStep1Good'/UNStep1Good  UNInfty1Row'/UNInfty1Row  UNCore'/UNCore  UNDensBandRow'/UNDensBandRow
    UNStep1GoodC'/UNStep1GoodC  UNCoreC'/UNCoreC: IDENTICAL(up to proof terms, reducible defeq)
SUB un_core_of_rows'/un_core_of_rows  un_bUniv_of_rows'/un_bUniv_of_rows
    UNDensInst.inst_core_band'/UNInst.inst_core_band  UNDensInst.inst_core_of_rows'/UNInst.inst_core_of_rows
    UNDensInst.inst_bUniv_band'/UNInst.inst_bUniv_band  UNDensInst.inst_bUniv_band_k'/UNKInst.inst_bUniv_band_k
    UNDensInst.inst_coreC_band'/UNKInst.inst_coreC_band: IDENTICAL(syntactic)
-- negative controls
CMP chk UNStep1Good' vs lib UNStep1GoodC': DIFFERENT     CMP chk not_UNStep1Good vs lib not_UNStep1GoodC: DIFFERENT
CMP chk unTrLocal_shift vs lib unTrLocalInit_shift: DIFFERENT   SUB UNCore' vs UNCoreC: DIFFERENT
CMP chk UNDens' vs lib UNDens: DIFFERENT
```
(Output lines grouped; each name printed on its own line in `cmp2.out`.) 31/31 pinned declarations equal the
check file; 13/13 primed pins/compositions/instances equal the merged source after the declared substitution:
T2201b none. `unDens'_freeConvST` differs only by `Type` → `Type*` (allowed). `UNDens'` second conjunct has the
`hbox ∧ hlip` shape with `c K Lp` fixed before `∀ᶠ n` (§29 (4), (6)).

## 3. Hidden hypotheses, vacuity, cycles
- `UNDens'` and all pins are `def`s built from `∧`/`∃`/`∀`; no structure, no hidden field. Imports: `PinsK`,
  `FreeConvRegular` (merged); no cycle. Helpers are `private` and prefixed `PinsDens_`; the 31 public declarations
  are exactly the pinned names (`grep -nE "^(theorem|lemma|def|noncomputable def)"`).
- `UNStep1Good`/`UNStep1GoodC` refutations carry the refuted pin plus data hypotheses only; the instances
  (§4) show those data hypotheses are met at `sz0` modulo other gates' owed pins, so the refutations are not vacuous.

## 4. Compiled nonempty instances (every endpoint theorem)
Data throughout: `sz0` (`N_0 = 2097152`), `𝔠 = 1/6`, `𝔡 = 1/10`, `E = E' = 0`, `δ = 1/2`, `k = 1`, `bump`.
```
$ sed -n '568,700p' PinsDens.lean | grep -nF <target>     # line numbers in the file, instance section
unDensBandRow'_of_row 693 696 | unDens'_freeConvST 639 645 | un_core_of_rows' 592 | un_bUniv_of_rows' 597 608
unDens_shift 662 | unTrLocal_shift 663 | unTrLocalInit_shift 687 691 | not_unDens'_unDensShift 664
not_UNStep1Good 672 | not_UNStep1GoodC 678 684 | un_dens'_msc_zero 584 593 637 665
```
Chain coverage of the rest: `UNDens'.toUNDens` (used at `:222` in `un_core_of_rows'` → `inst_core_of_rows'`),
`unDens'_msc_of_unDens` (`:196`, `:246` → `unDensBandRow'_of_row` example, `inst_bUniv_band'`), `unDensShift_of_le`
(`:318`, `:330`, `:363` → `inst_T2190a_family`, example `:688`), `un_msc_box_zero` (closed statement on the nonempty
box; used `:556-558` in the closed `un_dens'_msc_zero`). Repair `example`s (compiled with the module, §5):
- `:680` `not_UNStep1GoodC` at `(UNModel.band sz0).toC`, `msc`, `ρ = rhoSC 0`, `un_dens_msc_zero`; hypotheses kept:
  the refuted `UNStep1GoodC`, the owed `UNTrLocalInit sz0 … (fun _ => msc) 0 (1/2)` and `UNNormBandRow`.
- `:688` `unTrLocalInit_shift` at the same data, `h n = Nsz sz0 n ^ (-2)`; hypothesis kept: the owed `UNTrLocalInit`.
- `:694` `unDensBandRow'_of_row` at `κ = 1/10`, `E = 0` (`0 < 1/10`, `|0| ≤ 2 - 1/10` discharged by `norm_num`);
  hypothesis kept: the owed `UNDensBandRow`.
All deterministic hypotheses (`Admissible` via `sz0_adm`, `3 ≤ 3`, `|0| < 2`, `IsTestFun bump`, `UNDens'` via
`un_dens'_msc_zero`, positivity of `N^{-2}`, `N^{-2} ≤ 1`) are discharged. No `N = 0`, empty index, collapsed
window or `False` premise (the refuted pin as hypothesis of a refutation is its subject, not a vacuity).

## 5. Build, axioms, registry, hygiene
```
$ lake build RBM3D.Universality.PinsDens RBM3D.Test.Axioms
✔ [3338/3339] Built RBM3D.Test.Axioms (1.5s)
✔ [3339/3339] Built RBM3D.Universality.PinsDens (4.1s)
Build completed successfully (3339 jobs).
$ lake build      # full library at b818bb5 (root does not yet import PinsDens)
premises found by scanning: 109 (borrowed 1, owed 83, structural 23, refuted 2).
Build completed successfully (4003 jobs).
$ lake build RBM3D.Test.AuditNegative
info: RBM3D/Test/AuditNegative.lean:30:0: audit reverse test: an unclassified premise is caught (RBM.Audit.Fixture.FakePremise).
$ printf 'import RBM3D\nimport RBM3D.Universality.PinsDens\n#assert_rbm_axioms\n' > $S/Reg.lean; lake env lean $S/Reg.lean  # exit 0, 0 errors
premises found by scanning: 111 (borrowed 1, owed 83, structural 23, refuted 4)
registry: 2 borrowed + 126 owed + 59 structural + 4 refuted; 80 registered premise(s) carry nothing yet
  ledger: RBM.Univ.UNCoreC': 1  RBM.Univ.UNInfty1Row': 5  RBM.Univ.UNStep1Good': 0  RBM.Univ.UNStep1GoodC': 0
$ # Neg.lean: Axioms.lean:49-525 copied into namespace RBM.AuditNeg, commands renamed *_neg,
$ # owedProps line 175 := `RBM.Univ.UNStep1Good, `RBM.Univ.UNStep1Good', ...
$ lake env lean $S/Neg.lean ; echo exit $?
Neg.lean:481:0: error: axiom audit: 1 refuted premise(s) are also in `borrowedProps`, `owedProps` or `structuralProps`: [RBM.Univ.UNStep1Good]
exit 1
```
`#print axioms` (in `Cmp2.lean`) of all 23 theorems — the 15 targets of 2-5 and the 8 named instances — each:
`depends on axioms: [propext, Classical.choice, Quot.sound]`.
```
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom |native_decide" RBM3D/Universality/PinsDens.lean RBM3D/Test/Axioms.lean
RBM3D/Test/Axioms.lean:18:Any `sorry` (`sorryAx`) therefore breaks the build, and so does any new `axiom` that has
$ for x in <31 public names, toUNDens, UNDensInst, refutedProps, PinsDens>; git grep -nF -e "$x" main -- RBM3D RBM3D.lean
names checked: 34, names with hits: 0          # main = cef761a
```
The only hit is a docstring sentence, not code.

## 6. Paper deltas
Prove report (d): T2201a (`UNDens'` asks for uniform box regularity of `m_n`, stronger than Thm 2.7's
`ρ_N(E) ≥ κ`; Lean structure, no paper statement change), T2201b none (confirmed by §2), T2201c (registry class
`refutedProps`; merged docstrings of the four refuted pins still say "owed"). The repair adds no statement. Coverage
complete.

## 7. Per-target verdicts
| targets | statement | hidden/vacuity/cycle | instance | build/axioms | verdict |
|---|---|---|---|---|---|
| 1 vocabulary/pins (8 defs) | = check; = merged ∘ subst | none | via §4 | ok | PASS |
| 2 `toUNDens`, `unDens'_msc_of_unDens`, `unDensBandRow'_of_row`, `unDens'_freeConvST` | = check | none | ok (`:694` new) | ok | PASS |
| 3 `un_core_of_rows'`, `un_bUniv_of_rows'` | = check; = merged ∘ subst | none | ok | ok | PASS |
| 4 `unDensShift_of_le`, `unDens_shift`, `unTrLocal_shift`, `not_unDens'_unDensShift`, `not_UNStep1Good` | = check | none | ok | ok | PASS |
| 4 `unTrLocalInit_shift`, `not_UNStep1GoodC` | = check | none | ok (`:688`, `:680` new) | ok | PASS |
| 5 `un_msc_box_zero`, `un_dens'_msc_zero` | = check | none | closed | ok | PASS |
| instances (8); registry edit | = check / = ticket | nondegenerate | — | ok; neg. test fires | PASS |

No dispatcher sign-off needed.

## 8. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1 (carried from round 1, still true). `unTrLocal_shift`/`unTrLocalInit_shift` conclude the owed pins
  `UNTrLocal`/`UNTrLocalInit` from themselves, so `scanPremises` counts those two as concluded and lists them under
  "carry nothing yet" although they are still used as hypotheses; the owed found count stays 83. For the dispatcher:
  the "concluded by some theorem" rule is fooled by `P → P'` transport lemmas.
- O2. `refutedProps` lists `UNInfty1Row`, `UNCoreC` on the supervisor's argument (1651, 1.3), not on a compiled
  theorem, as the ticket specifies.
- O3. Merge note: `main` moved to `cef761a` after the branch point; it touches neither writable file, so the hub's
  step (A) 3-5 applies without conflict. The hub runs the full build with the new root import at merge.
