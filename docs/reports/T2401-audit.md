Auditor model: claude-opus-5-5

# T2401 audit (stage 2, round 1): BA-G5a 1b, `BA/GreenMinor{,2,3}.lean`. Sun Oct 11 05:48:12 UTC 2026
Inputs: ticket `docs/tickets/T2401.md`, Amend 1 (`T2401-amend-1.md`, H201), prove report `docs/reports/T2401-prove.md`, branch `t/T2401` at 8104042.
Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2401-audit1` (detached at 8104042; merge-base with main 1c25de0; main 1f79c74).
The pins are those of the probe `RBM3D/Probe/T2401Pins.lean` (aec5a16, 1a-audit round 2 PASS), with S4 = `GreenMinor_diff_pin'` (Amend 1 D2).
The 1b targets are those of (a′) D4: S1 (with `removal_cross*`, `offset_ne`), S2, S3, S4 (`diff'`), S6, the R1 tower, and the owed lines `BAFamGain`, `BAFAav`. S5/R6 belong to G5b.
Scratch files: `<scratchpad>/T2401/{pincheck,defcheck}.lean`, `defdiff.py`, `pub.py`.

## 1. Statements against the pins (independent check, script)
`pincheck.lean` imports `RBM3D.BA.GreenMinor3`. It holds the 16 probe `_pin` definitions verbatim (probe lines 80-196, 209-243, 274-299), in namespace `RBM.BA.AuditT2401`, then one `example : <pin> := @RBM.BA.<theorem>` each, then `#print axioms`:
```
$ lake env lean <scratch>/T2401/pincheck.lean; echo EXIT=$?
'RBM.BA.GreenMinor_removal' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_removal_crossL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_removal_crossR' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_removal_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_offset_ne' depends on axioms: [propext]
'RBM.BA.GreenMinor_tower' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_tower_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_good_of_event' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_Arow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_Xrow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_split_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_split_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_YA_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_YX_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_avgK_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenMinor_avg_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFamGain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAFAav' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```
So 16/16 pins elaborate against the merged-candidate theorems, with `example : GreenMinor_diff_pin' := @RBM.BA.GreenMinor_diff` (S4 carries `κ ≤ 1`, D2) and `GreenMinor_avgK_pin := @GreenMinor_avgK_eq`.
Pinned definitions (vocabulary, `BAFamGain`, `BAFAav`), first by text:
```
$ python3 -I <scratch>/T2401/defdiff.py        (whitespace-normalised def/structure blocks, probe vs RBM3D/BA/GreenMinor*.lean)
GreenMinor_T  GreenMinor_R  GreenMinor_Tower  GreenMinor_good  GreenMinor_YA  GreenMinor_YX  GreenMinor_a  GreenMinor_cY
GreenMinor_famGain  GreenMinor_avg  GreenMinor_avgK  GreenMinor_famA  GreenMinor_famX  BAFamGain  BAFAav : identical (15 lines, condensed)
differences: 0
```
Then definitionally. `defcheck.lean` re-elaborates the probe text of 11 defs as `*_probe` in the probe's `open` context, followed by `example : @X_probe = @RBM.BA.X := rfl` for good, YA, YX, cY, famGain, avg, avgK, famA, famX, BAFamGain and BAFAav:
```
$ lake env lean <scratch>/T2401/defcheck.lean; echo EXIT=$?
EXIT=0
```
Against the ticket's mathematics:
- S1 / (i), (ii): `greenMinor G w x y = G_xy - G_xw G_wy / G_ww` (`Green/EntryCore.lean:280`).
  - `|G^{(w)}_{xy} - G_xy| ≤ (2/κ)|G_xw||G_wy|` under `|G_ww| ≥ κ/2`.
  - Kronecker `M` gives `o(x) ≠ o(y) ⇒ M_xy = 0`.
  - Cross-offset forms give `(2/κ)δ‖G_wy‖`, `(2/κ)δ‖G_xw‖` and `(2/κ)δ²`. `offset_ne` covers `R_{β,o}` against `T_{β,o}`.
- S2: `‖G-M‖_max ≤ δ`, `κ ≤ ‖m‖`, `4δ ≤ κ`, `8m₀δ ≤ κ` and the tower give `|G^{(S)}_xy - M_xy| ≤ 2δ` and `|G^{(S)}_xx| ≥ κ/2` for all `S ⊆ R`, `|S| ≤ m₀`, `x, y ∈ T∖S`. This matches (a) T2.
- S3: the four exact identities hold under the `GreenCore_E3` hypotheses plus `m ≠ 0` and `G_uu ≠ 0`. The base bounds carry the pinned constants. `hD`/`g₀` is pinned but unused in `Arow_eq`/`Xrow_eq` (report (b) item 5).
- S4: graded bound `c_Y(|l|)(2δ)^{|l|+1}` for Nodup `l ⊆ R_{β,o}`, `|l| ≤ m₀`, `u = (β,o)`, `y` of offset `o` in another block. Route A constants, `κ ≤ 1`.
- S6: the averaged (E3) identity and the G1 split of `⟨M𝒦⟩_a` over all `b'`. This includes the two-block offset averages `avg_o 𝔛_{(b',o),(a,o)}` that G1 names.
- `BAFAav` quantifier order: `∀ κ ε 𝔡`, flow, `t`, `ε₀`, `BAGiiGEX(ε₀/2)` (D1), `Ψ` window, `(initialGT2)`, then `PrecL` uniform in `a`. There is no `∃ c` before the flow.
- `BAFamGain`: `∃ C ≥ 0` comes after `p` and before `∀ᶠ n`, with `ρ = 4δ_n`, `B = Cδ_n` and `M = K = 2p` (D3).
- Every target **PASS** on statement.

## 2. Vacuity, hidden hypotheses, cycles
- The only structure is `GreenMinor_Tower` (fields `base`, `step` = (4.9)). It is not a hidden assumption: `GreenMinor_tower` proves it for the principal-submatrix resolvents of any Hermitian `H` with `Im z ≠ 0`. `GreenMinor_tower_carrier` proves it at the BA carrier. Both are applied in the instances (§3).
- `GreenMinor_good` is a `def` (no fields). S2 discharges it from `‖Δ‖_max ≤ δ`.
- `BAFamGain` and `BAFAav` are owed `Prop`s, registered in `owedProps` (diff below). No theorem of the three files assumes them. Their external premise `BAGiiGEX(ε₀/2)` is an instance of the already-owed `BAGbEXPii` (`GreenMinor3.lean:915`, compiled).
- Imports, all on main:
```
$ grep -n '^import' RBM3D/BA/GreenMinor*.lean
GreenMinor.lean:6:import RBM3D.BA.GreenCore | GreenMinor2.lean:6:import RBM3D.BA.GreenMinor
GreenMinor3.lean:6:import RBM3D.BA.GreenMinor2 | :7:import RBM3D.Green.FlucIterGain | :8:import RBM3D.Green.MinorDiff     (condensed)
$ for m in BA/GreenCore Green/MinorDiff Green/FlucIterGain; do git cat-file -e main:RBM3D/$m.lean && echo "on main"; done   -> on main (x3)
```
- No module imports the probe. Verdict: no vacuity, no hidden hypothesis, no cycle.

## 3. Compiled nonempty instances (read in the files; every instance is in the same file as its theorem)
| target(s) | file:line | data; hypotheses left |
|---|---|---|
| removal, cross, removal_crossL/R/cross, offset_ne | GreenMinor:377,387,391,412 | `d=3,L=3,W=2`, `M=iI`, `Δ=ε(E_pq+E_qp)`, `ε=1/100`, `κ=1/2`, `w=q`, offsets `0≠1`; none |
| tower | GreenMinor:417; GreenMinor2:591; GreenMinor3:973 | `H=Δ` and `H=εJ_C`, `z=i`; none |
| tower_carrier | GreenMinor:426 | `sz0` (`L=4`, `W=32`), `flow_sz0`, `κ=1/2`, `t=1/2≤T₀`, every `ω`; none |
| good_of_event | GreenMinor2:591,625 | real resolvent `G=(εJ_C−i)⁻¹`, plus the hand tower; `κ=1/2`, `δ=1/100`, `m₀=3` (`8m₀δ=0.24≤κ`); none |
| YA_le, YX_le | GreenMinor2:591,630 | `g₀=1/10`, `s=m=i`, `δ'=1/100`, `Δ_{py}=c≠0` proved; none |
| Arow_eq, Xrow_eq, split_A, split_X | GreenMinor2:656 | BA carrier `sz0`, `t=1/2`, every `ω`, `u`, `y≠u`; `m≠0` from `BAflow_real`; none |
| avgK_eq, avg_split | GreenMinor3:888 | BA carrier `sz0`, `t=1/2`, every `ω`, `a`; none |
| diff (S4) | GreenMinor3:973 | real resolvent, real minors, `u=p`, `l=[q]` (length 1), `κ=1/2≤1`, `g₀=1/10`, `δ=1/100`, `Δ_{py}≠0` proved; none |
| BAFAav, BAFamGain (owed) | GreenMinor3:920,938 | `sz0`, `t≡1/2`, `ε₀=1/10`, `Ψ=W^{-1}` (window discharged by `rpow_le_rpow_of_exponent_le`), `τ=1/20`, `p=1`; left: the pin, `BAGiiGEX` (G6's `BAGbEXPii` instance, :915), `STInitialGT2gL` (premise) |
- No instance uses `N = 0`, an empty index, a collapsed window or a `False` premise. All instances compile (§4). **PASS.**

## 4. Build, axioms, hygiene, scope
```
$ lake build RBM3D.BA.GreenMinor RBM3D.BA.GreenMinor2 RBM3D.BA.GreenMinor3   (05:44:49-05:45:05 UTC; error/warning lines of the three modules: none)
✔ [3782/3784] Built RBM3D.BA.GreenMinor (3.6s)
✔ [3783/3784] Built RBM3D.BA.GreenMinor2 (4.4s)
✔ [3784/3784] Built RBM3D.BA.GreenMinor3 (4.9s)
Build completed successfully (3784 jobs).
EXIT=0
$ grep -c error <build log>  -> 0
$ grep -nE '\bsorry\b|\badmit\b|^\s*axiom |native_decide' RBM3D/BA/GreenMinor{,2,3}.lean; echo grep-exit=$?
grep-exit=1
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2401-check.lean   -> 0 error lines, EXIT=0
$ git diff --name-only main...HEAD
RBM3D.lean
RBM3D/BA/GreenMinor.lean
RBM3D/BA/GreenMinor2.lean
RBM3D/BA/GreenMinor3.lean
RBM3D/Probe/T2401Pins.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D.lean RBM3D/Test/Axioms.lean   (added lines only; no deletion)
+import RBM3D.BA.GreenMinor  +import RBM3D.BA.GreenMinor2  +import RBM3D.BA.GreenMinor3   (after the last import, before #assert_rbm_axioms)
+   `RBM.BA.BAFamGain, -- ... (T2401, BA-G5a, Amend 1 D3: owed; owner BA-G5b)
+   `RBM.BA.BAFAav, -- ... (T2401, BA-G5a, paper-delta T2401a, Amend 1 D1: owed; owner BA-G5b, consumer BA-G6b)
$ python3 -I <scratch>/T2401/pub.py RBM3D/BA/GreenMinor{,2,3}.lean
133 public declarations
not stem-prefixed and not in GreenMinorInst: ['RBM.BA.GreenMinor_Adm.mem_T', 'RBM.BA.GreenMinor_Adm.mono', 'RBM.BA.GreenMinor_Adm.ne', 'RBM.BA.GreenMinor_Adm.cross']
GreenMinorInst names (40): HV hp hq hm hε hMb hM hΔ hG hD hy ... green_hH hGex_sub hcc_norm hcc_ne hGΔ
$ for n in <93 non-Inst names> GreenMinorInst; do git grep -nw $n main -- RBM3D RBM3D.lean; done   (main 1f79c74)
hits only for the bare suffixes mono / ne / cross of `GreenMinor_Adm.*` (namespaced, not clashes); 0 for every full name and for `GreenMinorInst`
```
- Axioms: all 20 printed in §1 are within {propext, Classical.choice, Quot.sound}.
- Merged files edited: none besides the two root/registry additions. No frozen signature is touched.
- Scope: the five 1b files are the stage-1b writable files. `RBM3D/Probe/T2401Pins.lean` is the stage-1a probe, which may stay on the branch but must not be brought into main (the hub brings in only the five 1b files). **PASS.**

## 5. Paper deltas
- `docs/paper-deltas.md` has no T2401 entry yet. The report proposes these candidates ((d); G.9; (a″)):
  - `T2401a`: `BAFAav` is the averaged law for all `g ≤ Λ`, at `BAGiiGEX(ε₀/2)`.
  - `T2401b`: `famGain` word rows are restricted to the block.
  - `T2401c`: `a_0 = 2/κ`.
  - `T2401d`: `κ ≤ 1` in S4.
- These cover every Lean/paper difference I found. The abstract tower in S2/S4 generalises the paper's minors and is instantiated by R1, so it is not a delta.
- `m ≠ 0` and `G_uu ≠ 0` in S3 are implicit in the paper's (E3) algebra (`κ ≤ |m|`; `G_uu ≠ 0` from `Im z ≠ 0`). **PASS.**

## 6. Observations (no RETURN)
- **O1 (G5b scope).** These are not provided:
  - R1's `FinDepOffRows` / `applyOps` minor twin, listed in the G.8 R1 row;
  - `BddMeas`/`FinDep` for `GreenMinor_famA/famX`, hypotheses of `GreenMinor_famAvg_moment_pin`.

  Report (d) discloses this. Neither is a pinned 1b target ((a′) D4 lists "the tower for real minors"), and neither has an owed registry line. The G5b ticket should carry both explicitly.
- **O2.** The 40 public instance helpers live in namespace `RBM.BA.GreenMinorInst`. They are stem-prefixed through the namespace, not by name: rule (E) holds in substance, and no clash was found on main.
- **O3.** Report length: 572 lines in all, with the 1a sections at 419 lines, over the ticket's 300 (1a-audit O2). The 1b section is 153 lines, within 200.
- **O4.** Main moved past the merge base (1c25de0 → 1f79c74: T2407, T2409). At merge, the hub keeps both sides' import lines in `RBM3D.lean`. The full `lake build` at merge is the hub's step.

## 7. Verdict
**PASS** for every target: S1 (`removal`, `cross`, `removal_crossL/R`, `removal_cross`, `offset_ne`), R1 (`tower`, `tower_carrier`), S2 (`good_of_event`), S3 (`Arow_eq`, `Xrow_eq`, `split_A`, `split_X`, `YA_le`, `YX_le`), S4 (`diff` = `diff_pin'`), S6 (`avgK_eq`, `avg_split`), and the owed lines `BAFamGain`, `BAFAav`.
No dispatcher sign-off needed. O1 is a note for the G5b ticket.
