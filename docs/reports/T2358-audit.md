Auditor model: claude-opus-5-5

# T2358 audit, round 1 (Fri Oct  9 20:30:44 UTC 2026)

Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2358-audit1`, detached at `t/T2358` = da182dc; merge-base with `main` 1fcb883. `S` = auditor scratchpad `T2358/`. `F = RBM3D/Graph/LWProv.lean`. Inputs: ticket T2358, Amend 1, prove report.

**Overall verdict: BLOCKED (needs dispatcher sign-off).** The pinned target `locStepXProv_holds : LocStepXProv` does not exist on the branch. The prover (escalation round, Opus) reports the value-indexed pin as an obstruction and proposes re-pins (R-a, R-b, or dropping the target). The missing input is a dispatcher decision on the pin. Every other target passes.

## 1. Build, hygiene, diff, size
```
$ lake build RBM3D.Graph.LWProv ; echo exit=$?        (warnings listed are all in RBM3D/Green/LDEQuad.lean; 0 lines mention LWProv.lean)
✔ [3895/3895] Built RBM3D.Graph.LWProv (13s)
Build completed successfully (3895 jobs).
exit=0
$ git diff --stat main...t/T2358
 RBM3D/Graph/LWProv.lean | 1890 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1890 insertions(+)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " $F ; echo grep_exit=$?
grep_exit=1
$ grep -n "^import" $F
6:import RBM3D.Graph.LWEngine
7:import RBM3D.Graph.LWMoment
$ wc -l $F
    1890      (stop line 1950: not reached)
```

## 2. Axioms (`lake env lean $S/ax.lean`, `import RBM3D.Graph.LWProv`)
```
'RBM.Graph.lwProv_bridge' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lw_localregularXP' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwEngineProv_imp_localregularX' [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.prod' [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.comp' [propext, Classical.choice, Quot.sound]
'RBM.Graph.WExp.refl' [propext, Classical.choice, Quot.sound]
'RBM.Graph.ProvOut.Molecular.comp' [propext, Classical.choice, Quot.sound]
'RBM.Graph.CoverBy.comp' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWfD_union' [propext, Classical.choice, Quot.sound]
'RBM.Graph.valW_one' [propext, Classical.choice, Quot.sound]
'RBM.Graph.pvalW_one' [propext, Classical.choice, Quot.sound]
'RBM.Graph.LWProvInst.ProvOut.molecular_id' [propext, Classical.choice, Quot.sound]
'RBM.Graph.lwProv_locStepXProvPos_holds' [propext, Classical.choice, Quot.sound]
lw_localregularXP : LWEngineProv
locStepXProv_holds exists: false          (#eval env.contains `RBM.Graph.locStepXProv_holds)
```

## 3. Registry pre-check (no new premise)
```
$ lake build RBM3D ; tail -1 ; grep "axiom audit\|premises found"      (baseline, F not imported)
Build completed successfully (4170 jobs).
info: RBM3D.lean:402:0: axiom audit: 10524 theorems, 3078 definitions, 0 axioms in `RBM` ...
premises found by scanning: 133 (borrowed 1, owed 71, structural 42, refuted 6, superseded 13).
$ cat $S/reg.lean  ->  import RBM3D / import RBM3D.Graph.LWProv / #assert_rbm_axioms
$ lake env lean $S/reg.lean ; echo exit=$?
exit=0
1:axiom audit: 10627 theorems, 3125 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
134:premises found by scanning: 133 (borrowed 1, owed 71, structural 42, refuted 6, superseded 13).
```

## 4. Statements against the pin (probe `t/T2348:RBM3D/Probe/T2348Pins.lean` @ 9f3bd75)
The auditor's own doc-stripper (`$S/nodoc.py`: removes `/-- -/`, `/- -/`, trailing `--` comments, and blank lines):
```
$ diff <(sed -n "29,185p;291,310p" $S/probe.lean | python3 -I $S/nodoc.py) <(sed -n "39,220p" $F | python3 -I $S/nodoc.py)
24,28d23        < def LWExpData ... (the nine conjuncts)                                   [C3: definition removed]
31c26,29        < ..., LWExpData sz n z u m Sp M →
                > GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
                > (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
                > (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) →                       [C3 in WExp]
44c42, 48,49c46,47, 51c49   proof lines only (intro/rw with the nine named hypotheses)
55c53,56        < (hD : LWExpData sz n z u m Sp M) ...
                > (hG : GaussIBP sz) (hz : 0 < z.im) (hu : 0 < u) (hm0 : m ≠ 0) (hzm : ...)
                > (hSp : ...) (hSpT : Spᵀ = Sp) (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)   [C3 in WExp.prod]
59c60,61        proof term only
82c84           < ... LocStepX P LX →
                > ... LocStepX P LX → P.g.Normal →                                         [Amend 1]
```
(the hunks are abbreviated here; the full text is verbatim in the prove report (b), and the auditor's run gives the same hunks.) The nine inline conjuncts match the probe's `LWExpData` one by one, in order. Otherwise the only change is the namespace `RBM.Probe.T2348` → `RBM.Graph`. **Copied declarations: PASS.**

`lwProv_bridge` (F:243-247) against the ticket's C1 and its twin `lwMoment_fxyPow_val` (`LWMoment.lean:1748`):
```
theorem lwProv_bridge {d : ℕ} (sz : Sizes d) {p : ℕ} (hp : Even p) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ)
    (D : Finset (Zd d (sz.L n))) (x y : Idx d (sz.L n) (sz.W n)) :
    pvalW (fxyPowGraph p).pack (lwMoment_D sz n E t ω)
      (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ D then 1 else 0) ![x, y] =
      ((‖LWfD sz n E t ω D x y‖ ^ p : ℝ) : ℂ)
twin: theorem lwMoment_fxyPow_val {p : ℕ} (hp : Even p) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : ...) :
    (fxyPowGraph p).pack.val (lwMoment_D sz n E t ω) ![x, y] = ((‖LWf sz n E t ω x y‖ ^ p : ℝ) : ℂ)
```
The left side and the right side match the ticket's text. The hypotheses are the twin's (`Even p`), plus `D`. **PASS.**

`lw_localregularXP : LWEngineProv` (F:1690) has exactly the pinned type (`#check` above). `LWEngineProv` (F:178-184) is the probe's text and has no `Normal` premise, as Amend 1 states. **PASS.**

`locStepXProv_holds : LocStepXProv`: **absent** (`env.contains` false; `grep` finds it only in the module docstring F:17). `LocStepXProv` (F:171) is the probe's pin plus Amend 1, as required. In its place F proves `lwProv_locStepXProvPos_holds : lwProv_LocStepXProvPos`, where the maps are indexed by position (`∃ ps : List (ProvOutX P), ps.map (fun o => (o.tag, o.Q)) = LX ∧ …`). F also has the private conditional adapter `lwProv_locStepXProv_of_functional (hfun : lwProv_StepFunctional) : LocStepXProv`. Neither is the pinned target (CLAUDE.md §5.6). The position-indexed form is a different statement: it changes the conclusion of the pin. The adapter adds an unproved premise. **BLOCKED.**

## 5. Hidden hypotheses, vacuity, cycles
- `ProvOut`/`ProvOutX` are data structures (`Q`, `π`, `tag`) and carry no Prop fields. `ExtOK`, `Molecular`, `CoverBy` and `WExp` are `def … : Prop` and appear in conclusions only. `WExp`'s nine data premises are explicit binders (C3).
- `lw_localregularXP` does not depend on the missing target. Its proof goes through `lwProv_exists` and `lwProv_stepPos` (prove report (b): its closure check gives `LocStepXProv: false`), and its axioms are the standard three (§2).
- Amend 1's `P.g.Normal` is supplied where the recursion needs it (prove report (a)(iii): `hch`, `LWEngine.lean:703`; `fxyPowGraph_normal`). Inside F, the recursion (`lwProv_exists`) consumes it, and `lw_localregularXP` has no `Normal` premise left.
- No new external hypothesis. The registry premise count is 133 before and after (§3).

## 6. Compiled nonempty instances (namespace `RBM.Graph.LWProvInst`, F:1720-1795; compiled by the build in §1)
| ticket instance / endpoint | location | data | verdict |
|---|---|---|---|
| `ProvOut.molecular_id` | F:1723 | theorem for every `P` | PASS |
| `WExp.refl` at `fxyPowGraph 2` | F:1732 (inside `WExp.comp`) | `p = 2` | PASS |
| bridge, `p = 2`, `D = univ` = merged value | F:1763 | `lwWxInstSz` (d = 3), `n = 0`, `x = 0`, `y = Pi.single 0 1`, `ω = 0`; ends at `‖LWf …‖^2` | PASS |
| bridge, proper `D = {0}` | F:1777 | every `ω` | PASS |
| `lw_localregularXP` | F:1743 | `p = 2`, `c = 1/4` (`0 < c` by `norm_num`), `K0 = 1`, `d = 3`, `D = 10` | PASS |
| `WExp.prod` | F:1748 | all nine data hypotheses discharged by merged lemmas (`gaussIBP`, `lwWx_inst_im`, `lwWx_flow`, …); weights `1` or `1/2` | PASS |
| `LWfD_union` | F:1784 | `{0}`, `{1}` disjoint | PASS |
| `locStepXProv_holds` | none | the theorem does not exist | n/a (BLOCKED) |
None of the instances is degenerate: `p = 2`, `d = 3`, `D` is nonempty, and no premise is `False`.

## 7. Paper deltas
`grep -n "T2358\|LWProv\|LocStepXProv" docs/paper-deltas.md` finds nothing. The report proposes no candidate. The differences are C3, an inline encoding, and Amend 1, a `Normal` premise supplied by the recursion. Both are Lean encodings of the design's provenance layer and change no paper statement. Coverage is adequate for the delivered targets. Any re-pin of `LocStepXProv` (R-a/R-b) is also a Lean-internal encoding.

## 8. Verdict per target
| target | verdict |
|---|---|
| copied probe declarations (24) + `LWfD`, `LWfD_union` (C3 and Amend 1 only) | PASS |
| `lwProv_bridge` (C1) | PASS |
| `lw_localregularXP : LWEngineProv` | PASS |
| `locStepXProv_holds : LocStepXProv` (Amend 1 pin) | **BLOCKED**: not delivered |

**Exact missing input (needs dispatcher sign-off):** a decision on the pin `LocStepXProv`. The pin indexes its maps by the value `r ∈ LX` (`π : ∀ r ∈ LX, …`, consumed by `stepOuts` at each position). The construction yields one map per position, so a list with duplicate values `(tag, Q)` coming from different partition terms would need one shared map. Neither the ticket, Amend 1 nor design §2 addresses duplicate values. The options compiled or analysed on the branch:
- (R-a) re-pin as position-indexed `lwProv_LocStepXProvPos`, which is proved as `lwProv_locStepXProvPos_holds` (F:1867, instance F:1870);
- (R-b) keep the value-indexed pin with an added waved-cover premise (analysis only, not compiled);
- drop the target. None of the named R3 consumers (`LWEngineProv`, `WExp.prod`, `ProvOutX.Cover`, `LWfD`, `lwProv_bridge`) mentions `LocStepXProv`.
An automatic repair cannot proceed without this decision.

## Observations (no effect on the verdict)
- O1. Section 9 of F contains public non-pinned declarations with the `lwProv_` prefix (`lwProv_LocStepXProvPos`, `lwProv_locStepXProvPos_holds`, `lwProv_wildGraph`). They comply with §3 (E). If the dispatcher picks (R-a), the pinned name will differ from `locStepXProv_holds`.
- O2. F's module docstring (F:17) records the missing target. The hub merges only on PASS, so this branch should not merge as is.
