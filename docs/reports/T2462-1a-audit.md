Auditor model: claude-opus-5-5

# T2462 (U4s1) 1a-audit, design gate — Mon Oct 12 18:07:20 UTC 2026
Inputs: ticket `docs/tickets/T2462.md`, check `docs/tickets/checks/T2462-check.lean`, report `docs/reports/T2462-prove.md` (168 lines; section (a) = lines 3-89, 87 lines), branch `t/T2462` at `0a1203eb` (probe commits `bae738a`, `0a1203e` on `62eed82`), `main` at `e288560e`. Audit worktree: detached `../RBM3D-wt/T2462-1aaudit` at `0a1203eb` (build cache cloned). Scratch: `scratchpad/T2462/aud/`. Rules: CONTROL H250 (4), H252 (2), H183 (3); DECISIONS §269 (2), §270, §271 (4).

## 1. Probe recompile (own worktree)
`$ cd RBM3D-wt/T2462-1aaudit && lake env lean RBM3D/Probe/T2462Pins.lean; echo exit=$?`
```
@T2462_WardIdent : {d : ℕ} → {sz : Sizes d} → FlowFM sz → Prop
@probe_wardIdent_band : T2462_WardIdent_band
probe_thDecayK_band : T2462_ThDecayK_band
probe_profileK : ∀ (d : ℕ), T2462_ProfileK d
@probe_uKer_eq : ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2462_uKerDecomp C n
'RBM.BA.probe_wardIdent_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_thDecayK_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_profileK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_uKer_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_thDecay_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
Output identical to the prover's `probe_out.txt` (`diff`: only my `time` line differs). Probe 359 lines (≤ 400); `git diff --name-only main...t/T2462` = `RBM3D/Probe/T2462Pins.lean` only. `grep -nE "sorry|admit|native_decide|^axiom"` on the probe: no hit.

## 2. Pin diff, probe against check (`aud/pindiff.py`: each `def T2462_*` block, whitespace-normalized)
```
T2462_WardIdent : identical
T2462_WardIdent_band : identical
T2462_ThDecayK : identical
T2462_ThDecayK_band : identical
T2462_ProfileK : DIFFERS at char 183 | check: '…(∀ n, gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) → …' | probe: '…(∀ n, 0 ≤ gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) → …'
T2462_uKerDecomp : identical
ProfileK probe == check with E1 inserted: True
H252(2) literal present in probe ProfileK: True
```
`grep -c "∀ n, 0 < gK"` on the probe: 0. The only delta is E1 = the H252 (2) / §271 (4) text, verbatim. `0 < gK n` remains the per-index hypothesis it already was in the check text (not a `∀ n, 0 < gK n` clause). The window clause of `ProfileK` is at `sz.lam` only (no window crossing). So the H252 (2) case split on `sz.lam n = 0` / `> 0` is not needed here. At an index with `sz.lam n > 0`, Cmp gives `gK n > 0` (from `0 ≤ gK n` and `lam² ≤ A gK²`), so consumers can discharge the hypothesis.

## 3. Numerics reruns (prover scripts; outputs compared to the report's pasted blocks)
`$ for s in inst kernel profile ward; do python3 $s.py > aud/$s.out; diff aud/$s.out out_$s.txt; done; python3 -I aud/cmprep.py`
```
inst exit=0 ; diff vs prover out_inst.txt:  identical
kernel exit=0 ; diff vs prover out_kernel.txt:  identical
profile exit=0 ; diff vs prover out_profile.txt:  identical
ward exit=0 ; diff vs prover out_ward.txt:  identical
inst.py: report lines 27-40 == rerun output: True
kernel.py: report lines 44-48 == rerun output: True
profile.py: report lines 52-56 == rerun output: True
ward.py: report lines 60-62 == rerun output: True
```
Model check: `common.py`'s `sb_eig`, `Bparam`, `ellT`, `tailT`, `tailW` agree with `Defs/Block.lean:38-44` (`sbKernel`), `Defs/Tail.lean:44-53`, `Defs/Params.lean:32`. Key outputs: crossing max ratio/A = 1.0000 (A=1), 0.6917 (A=11); `(1-t)·rowsum` max 1.000000; Ward (zYU1) residual 3.25e-18; instance `d=3`, `sz0` n=1 (`L=8, W=1024, N=2^39`), with no WO/Bandwidth failure for n ≤ 200000.

## 4. Layout, cones, closures (`aud/clos.py`, `aud/cert.py` on the audit worktree)
```
Step5CasesGen closure 98 | has Induction.B45: False | has Induction.NewKLKL: False | BA/* : [] | stop-stem hits: GridDuhamelGen, GridDuhamelN, Path.Expansion
Step5KerGen closure 97 | has Induction.B45: False | has Induction.NewKLKL: False | BA/* : [] | (same three)
NewKLKLGen closure 103 | has Induction.B45: False | has Induction.NewKLKL: True | BA/* : ['RBM3D.BA.FlowPins', 'RBM3D.BA.MFixedPoint'] | (same three)
certificate cone (closure of 6 LWExpCert*): 168
  RBM3D.Chain.NewKLKGen in cert cone: False      RBM3D.Induction.Step5Kit in cert cone: True
  Step5Cases / WardII / Step5Kernel / NewKLKL / Chain.Step5Gen in cert cone: False
```
The closures agree with report line 134 (98/97/103; transitive `BA/*` 0/0/2). The three stem hits are inputs (`GridDuhamelGen` is a no-edit input of the ticket; `Path.Expansion` is reached through `Step5Gen`), not U4s2/U4s3/U5/V/X1 files, so they are not a cycle. Planned direct imports = the ticket's Layout list exactly; no direct `BA/*`.

## 5. Name clashes (19 final names + 3 module files; `git grep -c -F -w`, `git ls-tree`)
```
refs: main t/T2450 … t/T2466 (17 refs, incl. t/T2463 at 81ca99ae)
each ref: name hits 0, module files 0
TOTAL 0
```

## 6. Line estimate (`est2.py` rerun, `spans.py` rerun)
```
central (r=1.2)  CasesGen   933  KerGen   427  NewKLKLGen   651  total  2011
high (r=1.6)     CasesGen  1168  KerGen   555  NewKLKLGen   800  total  2523
central total 2011 > 1950: True ; 2.6 x central total = 5229 ; per file 2.6 x central: [2426, 1110, 1693] ; stop line 2000 per file
split U4s1a = Step5CasesGen 933 ; U4s1b = Step5KerGen + NewKLKLGen 1078
```
The spans agree with the ticket's per-file estimates (950 / 400 / 650). The probe calibration is 0.89.

## 7. Deliverables table (H250 (4); report lines 153-168, each reference checked by `sed -n`)
| # | deliverable | report line | audit |
|---|---|---|---|
| (i) | exponent table | 6-22 | met; rows 3-4, 8, 14 rerun (§3) |
| (ii) | concrete instance + script | 23-63; probe 259-329 | met; reruns identical (§3); Lean instances compile (§1) |
| (iii) | layout, cones, no `BA/*` | 134, 123 | met; reproduced (§4) |
| (iv) | D1, T2463 status, probe lines | 65, 110, 124 | met (see D1 below) |
| (v) | D2, probe lines, reader table, X1a | 66, 111, 125-127 | met; all ten D2 reader lines are mapped |
| (vi) | D3 table | 67, 128-130 | met; F5(a)(b)(c), F8, F9 and the domain `κ ≤ Im m` match `NewKLKGenHyp` (`Chain/NewKLKGen:383-411`) and `STNewKLKLAtgL'` (`Step5Gen:151-153`) |
| (vii) | scope table, 74 names | 131-133 | met; 17+20+4+2+22+2+7 = 74 |
| (viii) | hypothesis table | 69 | met |
| (ix) | UBA-C1 table | 70, 111, 113 | met; one crossing (probe line 203) |
| (x) | premise scan, registry | 136-138, 116-122 | met; the seven lines = ticket Registry |
| (xi) | `open private`, copies | 139-141 | met |
| (xii) | lines, 2.6×, split | 142-150, 68 | met (§6) |
| (xiii) | name clashes | 151 | met; reproduced (§5) |

## 8. Design decisions fixed at this 1a-audit
- **D1, Ward term.** Default confirmed. Target 7 = `T2462_WardIdent`, `T2462_WardIdent_band` and `T2462_stWardIIgL_of`, verbatim from the check. The probe proves the band form with one `exact stWardII_identity …`. T2463 (U1s1) is not merged (`t/T2463` at `81ca99ae`, state `proving`, 0 hits of `ZeroModeGen_WardCls` on `main`). T2463 has no 1a-audit, so this one fixes the one Ward text (§270 note (7)). The 1b re-checks the T2463 merge status at its start, as the ticket requires.
- **D2, kernel facts.** Target 9 = `T2462_ThDecayK` and `T2462_ThDecayK_band` verbatim from the check, and `T2462_ProfileK` = check text + E1 (probe lines 71-81). R1 (row sum `≤ 1/(1-t)`) is not adopted: the pinned `C₆/(1-t)` compiles and suffices for `ProfileK` (probe 244), and it asks less of the BA source. The target 12 (a) grep literal is read as the §271 (4) text, which supersedes `T2462.md:74`. The BA feed exists: `NewKLKBA_tail` (`BA/NewKLKBA:269`, private) covers both charge pairs with `0<g≤Λ`, `0≤u<1`, `BAReal`; `TwistStep2_lam0_sq` (`TwistStep2:740-741`) gives the comparison in squares form. X1a is merged: X1b reads `STThPropsg` (`CltGen:126`), U4s2/U4s3 read D2, and no bridge is needed in this row.
- **D3, NewKLKL.** No extra fact. D3 passes.
- **F2 (imports of `Step5KerGen`).** Copy the helpers under the stem (`newKLKL_tailT_shift`, the `zdistInf` helpers, `_SB_support`, `B45_row_thetaKer`: 97 lines, already counted in §6). Do not add `Induction/NewKLKL` or `Induction/B45`: the ticket's acceptance grep needs exactly the Layout imports, and B45 and NewKLKL are not in the closure (§4).
- **F3 (scan shape).** State `step5CasesGen_wardIdent_band` and `step5CasesGen_flowFacts_band` with conclusion head `Step5CasesGen_WardIdent` / `Step5CasesGen_FlowFacts` (`conclusionHead`, `Test/Axioms.lean:421-424`). The content is unchanged, since the `_band` pins unfold to these. Then no extra registry line is needed.
- **F4 (leaf move of the `NewKLKGen` BA example).** Not taken. `Chain/NewKLKGen` is outside the certificate cone (§4), but moving the example edits a no-edit file that is not among the sole writable files. Note (9) stands.
- **D4 split: confirmed.** The central is 2,011 > 1,950. U4s1a = `Chain/Step5CasesGen` (targets 1-7, the seven registry lines). U4s1b = `Chain/Step5KerGen` + `Chain/NewKLKLGen` (targets 8-11, no registry line). They are independent: T8 reads only `Step2Gen_USemigroup`, T9 only `ThDecayK` + Cmp, T10 only `NewKLKGenHyp`, T11 is U6's band instance, and none reads targets 1-7. U4s1b runs on its own branch without waiting. The dispatcher's U notice REQ is non-blocking.

## 9. Stop lines (ticket "Stop rules")
- File over 2,000 lines: not hit. High estimates are 1,168 / 555 / 800.
- Binding pin not provable, or a premise beyond (a)-(g): not hit. The D1/D2 pins and target 8 are proved in the probe; no premise was added.
- D2 or D3 has no form: not hit.
- Kernel, propagator or `Ugen` definition: not hit. The probe has no `Ring.inverse`, `Matrix.of` or `cycProd`.
- Direct `BA/*` or stop-list import: not hit (§4).
- Edit of a no-edit file: not hit; none is planned (F4 not taken).
- `withLam`, a second comparison form or another coupling: not hit in the planned statements. The one probe hit is in an instance (`probeSz1`, probe line 297); see O2.
- Unregistered `Prop` premise: not hit; the seven lines are as in the ticket.

## 10. Observations (not RETURN)
- O1 (prover's O1, confirmed; forwarded to the dispatcher). `Sizes.lam` has no sign (`Defs/Sizes.lean:138-146`), and `BAflowLam0 = √t0 · sz.lam` (`BA/FlowPins:386`). Under `BAFlow` or `STFlow`, a consumer of Cmp therefore needs `∀ n, 0 ≤ sz.lam n`, which §271 (4) takes for granted. T2462's targets and instances are unaffected: `ProfileK` reads `hcmp n` at one `n` only (probe 182), and its instances discharge `0 ≤ sz0.lam n`. It does matter to U4s2/U4s3/U4-BA (a)/U3-BA band and BA readings for a general `sz`.
- O2. The probe's non-band instance builds `probeSz1 := sz0.withLam …` (line 297). If it is copied into a new file, the target 12 (a) grep fails. For the 1b's non-band instance, take a coupling below `sz.lam` instead, e.g. `gK = fun n => sz0.lam n / 2`, `A = 4`.
- O3. 2.6 × the Step5CasesGen central is 2,426, above the 2,000 stop line. TLF-C1 does not require a backup file (central 933 < 1,000), but U4s1a has the least margin. The stop line stays binding in its 1b.
- O4. Report line 135 gives `Path.Expansion` as the only stem match. The pattern `Duhamel` also matches `GridDuhamelGen`/`GridDuhamelN` (inputs, not stop-list files). No statement is affected.

## Verdict
**PASS** (1a design gate). Every stage-1a deliverable (i)-(xiii) is met; no binding stop line is hit; the probe compiles with the standard three axioms; D1 and D2 are fixed as in §8, with E1 = H252 (2) verbatim; the pre-signed split U4s1a / U4s1b is confirmed. No dispatcher sign-off is needed for 1b (O1 is forwarded and non-blocking).
