Auditor model: claude-opus-5-5

# T2145 audit (S5-03, `RBM3D/Induction/Step5Cases.lean`) — Sun Oct  4 17:29 UTC 2026 (date -u)

Worktree `RBM3D-wt/T2145-audit1`, detached at `27a8824` (`t/T2145`).

## 1. Statement (targets against the ticket: verbatim copy of probe `7b2b789`)

```
$ F=RBM3D/Induction/Step5Cases.lean; S(){ git --no-optional-locks show 7b2b789:RBM3D/Probe/T2134Pins.lean; }
$ diff <(sed -n 36,698p $F) <(S | sed -n 1040,1702p) && echo EMPTY
EMPTY
$ diff <(sed -n 706,715p $F) <(S | sed -n 2263,2272p) && echo EMPTY
EMPTY
```
Outside these ranges: lines 1-35 (header, `import RBM3D.Induction.Step5Kit`, docstring, `open`s,
`namespace RBM.Gauss.Sizes`, `variable {d : ℕ} (sz : Sizes d)`), and 699-705/717
(`namespace RBM.Gauss.Step5Inst` + the `open` line of `Step5Kit.lean:593`, section heading, `end`).
These are the documented changes (namespace `T2134Inst` → `Step5Inst`). Probe `2255-2262` is the
merged `inst_skeletonI` (`Step5Kit.lean:636`), correctly not copied.

Elaborated target statements:
```
$ lake env lean $SCRATCH/ax.lean   (#check)
@Sizes.ST_step5_caseIII_of_pf : ∀ {d : ℕ}, Sizes.STPfStep5 d → Sizes.STStep5III d
@Sizes.ST_step5_caseII_of_pins : ∀ {d : ℕ},
  Sizes.STEtermsMid d → Sizes.STDuhamelII d → Sizes.STIniTermII d → Sizes.STWardII d → Sizes.STStep5II d
```
Matches the ticket's mathematics ("`STStep5III` from `STPfStep5`; `STStep5II` from `STEtermsMid`,
`STDuhamelII`, `STIniTermII`, `STWardII`"). All pins are merged defs (T2138, `Step5Pins.lean`):
```
Step5Pins.lean:209  def STPfStep5 (d) := STIngR5 d STReg5III (fun sz E s t => STPfConcl sz E s t)
Step5Pins.lean:273  def STEtermsMid (d) := STIngR5 d STReg5Mid (...)
Step5Pins.lean:325  def STDuhamelII (d) := STIngR5 d STReg5II (... STEtermsMidConcl → ...)
Step5Pins.lean:331  def STIniTermII (d) := STIngR5 d STReg5II (...)
Step5Pins.lean:346  def STWardII (d) := STIngR5 d STReg5II (...)
Step5Pins.lean:454  def STStep5II (d) := STStep5R d STReg5II
Step5Pins.lean:456  def STStep5III (d) := STStep5R d STReg5III
```
Regimes: `STReg5III`: `ilambda² ≤ 1-t` (case (iii), `3_5:1939`); `STReg5II`:
`ilambda²/L^d ≤ 1-t ∧ 1-s ≤ ilambda²/L²` (case (ii)); same `STIngR5` shape (fixed `κ ε 𝔡 Cd`
before `∃ 𝔠d`, then `∀ sz z s t`) for hypotheses and conclusion, so no quantifier reordering.

Declarations in the file (14 + 2 instances), none already in `main`:
```
$ grep -nE "^theorem " $F | cut -c1-60      (abridged to names)
39 st5_prec_mono'   57 st5_one_add_log_pow_le   84 st5_ellT_one   100 st5_Bctl_ge_III
120 st5_STWB_ge_III 146 st5_compare_IIIa  175 st5_compare_IIIb  281 st5_polylog_le_W
311 ST_step5_caseIII_of_pf  409 st5_mE_im_ge  418 st5_A15_le  438 st5_compare_IIward
532 st5_reg5II_mid  542 ST_step5_caseII_of_pins  707 inst_skeletonII  713 inst_skeletonIII
$ for n in <names>; do grep -rnE "(theorem|lemma|def|abbrev) $n( |$)" RBM3D | grep -v Step5Cases; done
(no output)
```

## 2. Vacuity, hidden hypotheses, cycles

- No structure introduced; hypotheses are the named `Prop` pins in the signatures only.
- No cycle: `STPfStep5` (resp. the four case-(ii) pins) take `STDecay … s`, `STDecayStrong … s`
  (at the initial time `s`) as premises and conclude `STPfConcl`/ingredient bounds, not
  `STStep5Concl`; the file imports only `RBM3D.Induction.Step5Kit` (merged, T2143 `85e43db`).
- Registry (DECISIONS §16, §20, §40): all seven pins already registered owed; no registry change
  needed and `RBM3D/Test/Axioms.lean` is untouched.
```
$ grep -nE "STStep5II|STStep5III|STPfStep5|STEtermsMid|STDuhamelII|STIniTermII|STWardII" RBM3D/Test/Axioms.lean | cut -c1-70
167:   `RBM.Gauss.Sizes.STStep5II, -- Step 5, case (ii): S5-02; S5-01 (T
168:   `RBM.Gauss.Sizes.STStep5III, -- Step 5, case (iii): from `STPfSte
170:   `RBM.Gauss.Sizes.STEtermsMid, -- `(S5WG+M000)`, `(S5WG+M)` (`3_5:
172:   `RBM.Gauss.Sizes.STDuhamelII, -- integrated hierarchy with `Q^{(1
174:   `RBM.Gauss.Sizes.STIniTermII, -- initial term `(zYU2)`, case (ii)
175:   `RBM.Gauss.Sizes.STWardII, -- Ward identity `(zYU1)`, case (ii);
182:   `RBM.Gauss.Sizes.STPfStep5, -- `lem:pf_step5`; proved internally
```
- External input: none new (no new premise; the limit inputs `W_n → ∞`, `N → ∞` come from the merged
  data `sz0`, `szB`).

## 3. Compiled nonempty instances

```
$ sed -n 706,715p $F
/-- Case (ii) from its ingredients, at `(szB, zB, 15/16, 31/32)`. -/
theorem inst_skeletonII (hE : STEtermsMid 3) (hD : STDuhamelII 3) (hI : STIniTermII 3) (hW : STWardII 3)
    (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step5II (ST_step5_caseII_of_pins hE hD hI hW) Cd hCd

/-- Case (iii) from `lem:pf_step5`, at `(sz0, z0, 0, 1/16)`. -/
theorem inst_skeletonIII (hPf : STPfStep5 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_step5III (ST_step5_caseIII_of_pf hPf) Cd hCd
```
Each endpoint is applied at concrete d = 3 data through the merged `inst_step5II/III`
(`Step5Kit.lean:603,608` → `inst_ing5_II/III` with `szB_reg5II`, `sz0_reg5III`, the flow,
`0 ≤ s < t ≤ lemT`, and `STConStInd` discharged there; `κ=ε=𝔡=1/10`, `𝔠=1/6`). Regime (ii) at
`szB` (`L=4`, `ilambda=1`): `1/64 ≤ 1/32 ≤ 1/16 ≤ 1/16`; regime (iii) at `sz0`: `ilambda_n² ≤ 15/16`.
Nondegenerate (`L ≥ 4`, `W_n → ∞`, `s < t`). Remaining hypotheses are other gates' pins
(`STEtermsMid`, `STDuhamelII`, `STIniTermII`, `STWardII`, `STPfStep5`) and the stochastic premises
inside `InstIng5Concl` (`STKbound`, …, `STLKU`), the same form as the merged, audited
`inst_skeletonI` (T2143). `Cd` is a free positive parameter. Compiles (§4).

## 4. Build, axioms, hygiene, diff scope

```
$ lake build RBM3D.Induction.Step5Cases 2>&1 | grep -E "error|sorry|Build completed"; echo exit=$?
Build completed successfully (3776 jobs).
exit=0
$ lake env lean $SCRATCH/ax.lean        (#print axioms, all 16 declarations)
'RBM.Gauss.Sizes.ST_step5_caseIII_of_pf' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.ST_step5_caseII_of_pins' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_skeletonII' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step5Inst.inst_skeletonIII' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean $SCRATCH/ax.lean 2>&1 | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$"
16
$ grep -nE "sorry|admit|native_decide|^axiom" $F || echo no-hit
no-hit
$ git --no-optional-locks diff --name-only main...HEAD
RBM3D/Induction/Step5Cases.lean
$ grep -n "^import" $F
6:import RBM3D.Induction.Step5Kit
```
Only the sole writable file is touched; no frozen signature changed; does not import `RBM3D`.
(Full `lake build` with `#assert_rbm_axioms` is run by the hub at merge.)

## 5. Paper deltas

The copied statements are unchanged from the T2134 probe whose pins were signed off as
D315–D324 (DECISIONS §40); no new Lean/paper difference is introduced here.
```
$ grep -n "D315" docs/paper-deltas.md | cut -c1-60
1271:## D315–D324 · Step 5 钉文（2026-10-04，T2134a–j；ST-D4 设计，3668596；
```

## Observations (no verdict effect)

- O1. The copied helpers (`st5_*`) are public, not `private`; they carry the `st5_` prefix used by the
  merged `Step5Kit` and the ticket asks for a verbatim copy, so this follows the ticket.
- O2. Docstring of `STPfStep5` (`Step5Pins.lean:207`, not this ticket's file) says "borrowed";
  the registry (`Test/Axioms.lean:182`) says owed. Docstrings are not evidence (§5.7); for the dispatcher.
- O3. Prove report §(b) registry line list is not in name order; lines are correct (§2).

## Verdicts

| Target | Verdict |
|---|---|
| 1. probe `1040-1702` copy: `ST_step5_caseIII_of_pf`, `ST_step5_caseII_of_pins` and comparisons | PASS |
| 2. `inst_skeletonII`, `inst_skeletonIII` | PASS |

Ticket T2145: **PASS**. No dispatcher sign-off needed.
