Auditor model: claude-opus-5-5

# T2080 audit (round 1) — ST2-03 `Induction/Step2Events.lean`

Written Sat Oct  3 22:57:31 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2080-audit1`,
detached at `t/T2080` = `342d4a0`; merge-base with `main` = `a91ac93`. Scratch: `scratchpad/T2080/` (`$S`).
Targets: (A) the verbatim move of probe `0362cbc` §9, §10 (Amend 1 D3), §11 up to `end More` (47 theorems, 2 defs);
(B) `STLWB_of_LWterm`, (C) `STLWT_of_LWtermExp` (Amend 1 signatures).

## 1. Statements

(B), (C) against the Amend 1 pin text:
```
$ printf '<Amend 1 text>' > $S/pin.txt; grep -hE '^theorem (STLWB_of_LWterm|STLWT_of_LWtermExp)' Step2Events.lean | sed 's/ := by$//' > $S/lean.txt
$ diff $S/pin.txt $S/lean.txt && echo "bridge statements = Amend 1 pins"
bridge statements = Amend 1 pins
```
i.e. `theorem STLWB_of_LWterm {d : ℕ} (hd : 3 ≤ d) : LWterm d → STLWB d` and
`theorem STLWT_of_LWtermExp {d : ℕ} (hd : 3 ≤ d) : LWtermExp d → STLWT d`. The pins `LWterm`, `LWtermExp`
(`Graph/LWPins.lean:240,290`), `STLWB`, `STLWT` (`Induction/Step2Defs.lean:406,421`) are merged and untouched
(diff file list in §4). Both proofs are complete: neither takes any hypothesis besides `hd` and the LW pin
(by signature). Read of the proof: (1) `STB_EGt_eq_LWE` (`STEGt = LWE` pointwise, from `Matrix.trace_mul_comm`
on six factors plus `ring`); (2) `Ψ' = max(Ψ n 0, W^{-d/2})`, `Φ n r = Ψ n ⌊r⌋₊`, with `ε₀ ≤ d/2` derived
(`STB_eps_le`) from `STPsiClass`(3) and `W → ∞` (`ST_W_tendsto`, from `STFlow`); (4) `ℓ' = 0` for `n < N₀`;
transport of `≺` (`STB_prec_dom`) along an eventual pointwise domination. These are the ticket's differences (1), (2), (4)
plus D1/D2 of Amend 1, and nothing else. The bridges are conditional adapters (pin ⇒ pin) by the ticket's design;
the report says so (§(b) narrative, last line).

(A) the moved text against the probe (ranges 2128-2242, 2258-2263, 2308-2330, 2526-3571 vs file lines 40-1238):
```
$ diff $S/moved_probe.txt $S/moved_file.txt | grep '^[<>]' | sed 's/[[:space:]]*$//' | sort | uniq -c | sort -rn
  10 > namespace RBM.Gauss.Sizes
  10 > end RBM.Gauss.Sizes
  10 >
   9 < namespace RBM.Probe.T2039
   9 < end RBM.Probe.T2039
   2 > open RBM RBM.Loop RBM.Path
   2 >   have hb := (STBctl_pos sz n hlt).le
   2 <   have hb := (ST2_Bctl_pos sz n hlt).le
   2 <
   1 > variable {d : ℕ} (sz : Sizes d)
   1 > section ScaleMoved
   1 > end ScaleMoved
   1 >     (STBctl_pos sz n (lt_of_le_of_lt (tt n).2.2 (lt_of_le_of_lt (htT n)
   1 < time `t`), into a `w.h.p.` statement of the grid walk simultaneously for all grid indices
   1 < open RBM RBM.Loop RBM.Probe.T2039 RBM.Path
   1 < every time section `tt n ∈ [s_n, t_n]` (the shape of the light-weight and martingale pins at a
   1 < `ST_grid_whp_of_sections` turns single-time domination statements of the model, available at
   1 < `j ≤ K_n` and all labels (`ST_whp_grid` of section 5 with the per-time `≺` of `ST_PT_of_sections`). -/
   1 < /-! ## 9. The good event of the grid walk from the pins (`3_5:537–577`)
   1 <     (ST2_Bctl_pos sz n (lt_of_le_of_lt (tt n).2.2 (lt_of_le_of_lt (htT n)
```
Only namespace/`open`/section wrappers, the §9 header comment (moved into the file header), and the 3 renamings
`ST2_Bctl_pos → STBctl_pos` permitted by the ticket. No statement line differs. Since the probe's `open RBM.Probe.T2039`
is dropped, the probe definitions the moved text uses now resolve to merged ones; they are textually identical:
```
$ python3 $S/defcmp.py $S/probe.lean <worktree> $S/moved_probe.txt   # comments/whitespace stripped, ST2_Bctl→STBctl
probe defs used in moved text, also in library: identical 23 different 0
```
Verdict on statements: (A) verbatim; (B), (C) equal to the amended pins.

## 2. Vacuity, hidden hypotheses, cycles

- No new `structure`; the new Prop defs are `STScaleInv` (probe §10, moved by Amend 1 D3: `∀` time section, `∀ D > 0`,
  `STLWassmExp` at `ℓ_n = Kf n (tt n)`) and `STBdata` (probe §11; not used as a premise in this file:
  `grep -n STBdata` hits only the docstrings and its definition). Both are the probe's text.
- Imports: `RBM3D.Induction.Step2Core`, `RBM3D.Graph.LWPins` only (no `import RBM3D`); all dependencies merged; no cycle.
- External hypotheses: none new. `LWterm`/`LWtermExp` (LW gate), `STLWT`, `STEMn2Exp`, `STGridMart`, `STDecay`,
  `STStep1Weak` are merged pins; `STScaleInv` is registered `owedProps` (ST2-04/ST2-05).
- Registry diff (`RBM3D/Test/Axioms.lean`): two comment edits (`STLWB`, `STLWT`, `STGoodAt`) and two new `owedProps`
  entries `STStep1Weak`, `STScaleInv`; `STGoodAt` stays owed (`ST_good_prob` bounds `P(¬STGoodAt)`, it does not prove it:
  checked against its signature, conclusion `pathP {ω | ¬ STGoodAt …} ≤ ofReal (N^{-D'})`).

## 3. Compiled nonempty instances

```
$ grep -oE '^theorem [A-Za-z_0-9]+' Step2Events.lean | … | while read n; do grep -cw $n <section Instances> … ; done
theorems: 47; examples in Instances: 49
$ awk '/^example/{e=1} /^private |^\/--|^\/-!|^end /{e=0} e' inst.txt > ex.txt; <same loop over ex.txt>
done            # no theorem is applied only inside a private helper: every one of the 47 occurs in an `example`
$ grep -n "False\|sz0.size n = 0\|Fin 0\|Empty" inst.txt
                # (no output)
```
Data: `d = 3`, merged `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `size ≥ 17` proved), `z0`, `flow_z0`, `s ≡ 0`, `t ≡ 1/16`,
`K ≡ 16`, label type `Fin 1`/`Fin 2`. Bridges: `example (h : LWterm 3) (hI : STInitialGT2 …) (hA : STLWassm …) :=
inst_LWB (STLWB_of_LWterm (by norm_num) h) hI hA`, and the `LWtermExp 3`/`inst_LWT` analogue; `3 ≤ 3` discharged,
`inst_LWB`/`inst_LWT` (merged, `Step2Defs.lean:1009,1044`) discharge `STFlow`, `t` range, `ε₀ = 1/20`, `Ψ0 ∈ STPsiClass`;
the remaining hypotheses (`LWterm 3`, `STInitialGT2`, `STLWassm(Exp)`) are owed pins of other gates.
Event examples (`ST_LW_sections`, `ST_event_weak/lw/mg/init`, `ST_good_prob`) keep only `STLWT 3`, `STEMn2Exp 3`,
`STStep1Weak`, `STDecay`, `STScaleInv`, `STGridMart 3`; deterministic premises (cardinalities, `hBd`, `hsmall`,
`hKcap`, `hρ`, `hrem`, `hΔ`) are discharged at `sz0` with constants `cB = 1/2`, `c = 1/4`, `δ₀ = 3`, `ε₁ = 1/8`, `D = 1`.
No degenerate data found.

## 4. Build, axioms, hygiene, files

```
$ lake build RBM3D.Induction.Step2Events 2>&1 > $S/build.txt; grep -n "error\|Build completed\|exit=" $S/build.txt
215:Build completed successfully (3747 jobs).
216:exit=0
$ (echo 'import RBM3D.Induction.Step2Events'; sed 's/^/#print axioms RBM.Gauss.Sizes./' pub.txt) > ax.lean   # 49 public names
$ lake env lean $S/ax.lean > ax.out; echo exit=$?; grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out
exit=0
49
$ grep -v "depends on axioms: \[propext, Classical.choice, Quot.sound\]" ax.out | head      # (no output)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom ' Step2Events.lean | wc -l
       0
$ git diff --name-only main...t/T2080
RBM3D/Induction/Step2Events.lean
RBM3D/Test/Axioms.lean
$ <name loop> git grep -n -w "$x" main -- 'RBM3D/*.lean' ':!RBM3D/Probe' | grep -E "(theorem|def|lemma|abbrev) $x\b"
checked 49 names against main 4f186cf: declaration clashes listed above (none if empty)
```
Build warnings are linter-only (line length, unused variables, 3 deprecations). Full `lake build` (registry
`#assert_rbm_axioms`) not run here: the hub runs it at merge.

## 5. Paper deltas

Report (d) proposes `T2080a` (`3 ≤ d` on the bridges), `T2080b` (`Ψ' = max(Ψ_t(0), W^{-d/2})`), `T2080c`
(`Φ_t(r) = Ψ_t(⌊r⌋₊)`, `C₁' = C₁2^{C₂}`), `T2080d` (finite-`n` change of `ℓ`), `T2080e` (namespace, renaming,
§10 declarations now here), `T2080f` (registry classes). These cover every difference found in §1 (difference (1) is a
definitional identity proved in Lean, not a statement difference). Coverage complete.

## Observations (no verdict effect)

- O1 (hub, merge): `main` moved to `4f186cf` after the branch point; T2079 added `RBM.Ind.Step1TargetV3` to `owedProps`
  next to the lines this branch edits. `git merge-tree --write-tree main t/T2080` reports
  `CONFLICT (content): Merge conflict in RBM3D/Test/Axioms.lean`. Bringing in the branch's `Axioms.lean` wholesale would
  drop the `Step1TargetV3` line; the merged file must keep both main's line and this branch's 2 new entries / 3 comment edits.
- O2: report (b) says the full build ran "after the rebase onto main `a91ac93`"; that is the current merge-base, not the
  current `main`. No effect on this module's statements, build or axioms.
- O3: `STScaleInv` has no standalone nonempty witness; it is a registered owed premise (ST2-04/05), taken as an
  example hypothesis, as CLAUDE.md §4 step 2 allows for pins of other gates.

## Verdicts

- (A) moved declarations (47 theorems, 2 defs): **PASS**.
- (B) `STLWB_of_LWterm`: **PASS**.
- (C) `STLWT_of_LWtermExp`: **PASS**.
- Ticket T2080: **PASS** (no dispatcher sign-off needed; see O1 for the merge).
