Auditor model: claude-opus-5-5
# T2449 audit, round 2 (BA-DMN design, report only): PASS

Written Mon Oct 12 13:18:44 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2449-audit2`, detached at `t/T2449` = `921369b`. Audited: `docs/reports/T2449-design.md` (158 lines, main worktree), the probe `RBM3D/Probe/T2449Pins.lean` (397 lines), the round-1 defects D1, D2, and the ticket's acceptance list. Scratch: scratchpad `T2449/a2_*`.

## 1. Build, axioms, hygiene, diff

```
$ git rev-parse HEAD
921369b2d3a93acf192b44a66e4b48c1842e0646
$ lake build RBM3D.Main.BandTerminal RBM3D.BA.UNPins RBM3D.BA.TwistChain RBM3D.BA.MReg RBM3D.Universality.GUEPhase.RandomLayerB
Build completed successfully (4173 jobs).
$ lake env lean RBM3D/Probe/T2449Pins.lean > a2_probe.out 2>&1; echo "exit $?"; wc -c a2_probe.out
exit 0
       0 a2_probe.out                      (no errors, no warnings)
$ wc -l RBM3D/Probe/T2449Pins.lean
     397
$ grep -nE "sorry|admit|native_decide|^axiom|inductive" RBM3D/Probe/T2449Pins.lean ; echo grep-done
grep-done
$ # scratch copy (a2_ax.lean) + #print axioms of every public probe theorem
'RBM.BA.flowG_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.pad_subseq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_dom_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_Ed_of_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_flowG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_domG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_mlout' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.UNLocAvgBA_of_BAEnd_locSCL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_of_BAMLOutTL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unMLOutBA_of_V' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff --stat main...t/T2449
 RBM3D/Probe/T2449Pins.lean | 397 +++++
 1 file changed, 397 insertions(+)
$ # name clash: (def|theorem|lemma|abbrev) <name> outside Probe/T2449, for RBG_Que RBG_Prod RBG_Flow RBG_Dom BAfT BAfE
$ #   BAEd BAMO BAEnd_locSCL BAEnd_QDiffL BAEnd_decolL BAThm27L ba_flowG ba_domG ba_mlout pad_subseq BAendDom BAprof BAGz BAMz
RBG_Que 0;RBG_Prod 0;RBG_Flow 0;RBG_Dom 0;BAfT 0;BAfE 0;BAEd 0;BAMO 0;BAEnd_locSCL 0;BAEnd_QDiffL 0;BAEnd_decolL 0;BAThm27L 0;ba_flowG 0;ba_domG 0;ba_mlout 0;pad_subseq 0;BAendDom 0;BAprof 0;BAGz 0;BAMz 0;
```
The private helpers (`ba_t0_ineq`, `κ₀_pos`, `zp_im`, `S0_pt`, `ηQ_mem`) are covered by the empty warning output (a `sorry` would print "declaration uses 'sorry'"). The design report is in the main worktree (CLAUDE.md §2: reports live there); the probe is never merged. Both within 400 lines.

## 2. What changed since round 1 (`5c0c593` → `921369b`), by script

```
$ python3 -I a2_cmp.py a2_old.lean a2_new.lean     # whitespace-normalised declaration blocks
unchanged 39
changed []
removed ['zE']
added ['RBG_Que', 'κ₀', 'κ₀_pos', 'zp', 'zp_im', 'S0_pt', 'ηQ_mem']
```
Every declaration that round 1 checked (the end pins `BAEnd_locSCL/QDiffL/decolL`, `BAThm27L`, the step pins, V3, `RBG_Flow/Dom/Prod`, the proved BA instances) is token-identical, so the round-1 statement findings (round-1 report §3, §5) carry over; spot re-check: `band_terminal : UNL32 → decol ∧ locSC ∧ QUE ∧ BUniv ∧ QDiff` (`Main/BandTerminal.lean:104`) has the order of `BAThm27L` (probe 217-218).

## 3. D1: `Que′` = `RBG_Que` (probe 58) against T4 `RandomLayerB_Que` (`RandomLayerB.lean:166-181`)

```
$ sed -n 166,181p RandomLayerB.lean | tr -s ' \n' '\n\n' > a2_T4.tok ; sed -n 58,69p T2449Pins.lean | tr -s ' \n' '\n\n' > a2_Que.tok ; diff a2_T4.tok a2_Que.tok
2c2   < RandomLayerB_Que  > RBG_Que
10a11,22  > (Ed : ℝ → Sizes d → ℕ → ℂ → Prop)
13,15d24 / 18c27,28   < (fE fT : ∀ _ : Sizes d, ℕ → ℂ → ℝ)   > (fE fT : Sizes d → ℕ → ℂ → ℝ)   (same type)
79a90     > κ'                          (new quantified margin, beside the bulk κ)
96a108,111 > κ' → 0 <                   (0 < κ')
167c182,183 / 171,175c187   < |fE sz n (z n)| ≤ 2 - κ   > Ed κ' sz n (z n)
```
(diff output condensed to one line per hunk; tokens verbatim). Nothing else differs: the bulk `K.bulk sz κ`, `τU ≤ ouTauMax`, `0 ≤ t ≤ t^*`, `z_n = E_n + iη_Q` eventually, `0 ≤ (1-ζ)fT ≤ fT < 1`, `KF`, `MO`, `PB`, and the conclusion `∀ τ > 0, ∀ᶠ n, RandomLayerB_QueAt K P sz 𝔡 n (E n) (t n) τ` are T4's. This is exactly design §1.3 E-d (line 44). **PASS (statement).**

Instance (probe 378-389): `κ = clsκ`, `κ' = κ₀ = (πκ_*)^5/2048 > 0`, `τU = 1/1000`, `ouTauMax (1/6) (1/10) = min(min(1/72, 1/720), 1/100) = 1/720` (`ZeroModeProfile.lean:78`), `t_n = ouTStar = N^{-1+τU} > 0` (`Pins.lean:142`), `E_n = E_*` (`cls_bulk`), `z_n = E_* + iη_Q` (`rfl`, every `n`), `0 < η_Q ≤ 1` proved (`ηQ_mem`, probe 365), `Ed κ₀` and `fT < 1` from `S0_pt` (probe 311, which uses `ba_dom_of_bulk`, `ba_Ed_of_im`, `BAt0_lt_one`), `0 ≤ (1-ζ)fT ≤ fT` from `0 < e^{-t} ≤ 1`. The premises left are those after `∀ Kt`: `KF`, `PB` (C5's producer `Prod′`) and `BAMO` (from V's `UNMLOutBA`), and the profile `P` (C3 owes `UNOUProfile.ba`) is a variable: all other gates' outputs. Data nondegenerate (`t_n ≠ 0`, `η_Q > 0`, bulk nonempty). **D1 resolved: PASS.**

## 4. D2: the `Prod′` instance (probe 330-363)

`RBG_Prod` is unchanged (§2). Its token diff to T2 (`:132-150`): `|fE| ≤ 2-κ ↦ Ed κ'`, `κ ↦ κ'`, `etaT (fE) (fT) ↦ √fT · Im z`, `gueScale … ↦ N · (√fT · Im z)`; `gueScale E n u = N · etaT (E n) u` (`Grid.lean:84`), so the substitution is consistent. In the instance, `r2` (probe 338), `r3` (348), `r4` (352) are now `have`s proved from `S0_pt` (`κ₀/(κ₀+1) ≤ fT`, `1 - fT ≤ η/κ₀`), `η_n = N^{-19/20}` and `S0_adm.2.2.1` (`N → ∞`) with `tendsto_rpow_atTop`, `tendsto_rpow_neg_atTop`; `h730` holds at `t1 = fT` (`fT - t1 = 0 ≤ …`); `BAMO` is `ba_mlout` from `UNMLOutBA` (V) with `Fl = BAFlow` from `ba_domG` at `ε = 1/20`. Only `KF`, `PB` (C5 pins, quantified as variables) and `hML : UNMLOutBA 3` (V) remain. Compiles (§1). **D2 resolved: PASS.**
Observation: `t1 = fT` is the `t = 0` end of the OU time range (`t1 = (1-ζ(t))fT`, `ζ(0) = 0`), an admissible point of the window, not a collapsed index set; no change asked.

## 5. Per-target verdicts (acceptance list)

| item | verdict | evidence |
|---|---|---|
| probe compiles, axioms, no `sorry`/`axiom`/`inductive` | PASS | §1 |
| diff = probe only (+ report in main worktree) | PASS | §1 |
| line 1 of design: C5 verdict (fails), rows (6), total central (5,090); MN0 before MN1 | PASS | design:1, §1 at :18, §2 at :55 |
| MN0 (E5 fails; repair C5g; no U/V/merged-pin change) | PASS | round 1 §2 (independent scripts, conj. 4 mismatch, Dom at g = 10); repaired pins all new names (§1 clash grep) |
| MN1 coverage, one row per endpoint + no-producer list (3 items) | PASS | design:57-86; statements unchanged (§2) |
| every pin in report is in the probe with a `d = 3` instance | PASS | `RBG_Que` added (§3); `Prod′` instance complete (§4); other instances unchanged (probe 277-326, 391-393) |
| lesson 10 (signature carries every exponent-row quantity) | PASS | design:90-99; `RBG_Que` adds `κ'` to the signature |
| MN2, MN3, MN4 (row table with file/deps/lo-c-hi/role; N1 fate: re-homed) | PASS | design:101-144; unchanged since round 1 |
| design line numbers match `921369b` | PASS | checked: 35, 40, 45, 58, 79, 98, 116, 131, 144, 192, 200, 213, 217, 220, 259, 264, 277, 286, 295, 301, 320, 330, 365, 378, 391, 393 |

## 6. Paper deltas

Unchanged from round 1: `T2449a` (explicit form, law `seqP (sz.withLam 0)`), `T2449b` (UN-51 interface false at BA; repaired inputs `RBG_*`, now including `Que′`, carry the margin `κ'`), `T2449c` (`distB`), plus D403/D500/D503 inherited. `RBG_Que`'s only change (the margin `κ'`) is covered by `T2449b` (design:158). PASS.
Observation (carried from round 1): `T2449b` calls the `|Re z| ≤ 2-κ` of `zztE_BA` "the typo of T2001g", while `docs/paper-deltas.md:1494` (D535) says it is the paper route's condition; the dispatcher should reconcile the wording when numbering. No statement changes.

## Verdict

**PASS.** D1 and D2 of round 1 are repaired; no statement of round 1 changed; build, axioms, hygiene, diff, instances and paper-delta coverage pass. Report-only merge of `docs/reports/T2449-design.md` (the probe stays on `t/T2449`). The design itself requests dispatcher decisions (design §7: row C5g, N1 re-homing, N3 writable files, V3, opening REQ); these are the ticket's intended output, not a sign-off condition of this audit.
