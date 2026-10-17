#!/usr/bin/env python3
"""Generate the step-3 comment clean-up tickets and their check files (dispatcher tool, run in the cloud;
outputs copied to the device).  Usage: gen_comment_tickets.py <scopes.json> <outdir> <time> <t2523hash> <rework>"""
import json, sys, os

scopes = json.load(open(sys.argv[1]))
out = sys.argv[2]; TIME = sys.argv[3]; H = sys.argv[4]; RW = sys.argv[5]
first = scopes[0]['n']; last = scopes[-1]['n']
os.makedirs(os.path.join(out, 'checks'), exist_ok=True)

PAT = (r"T2[0-9]{3}|DECISIONS|paper-delta|\bD[0-9]{1,3}\b|\b(1_2|3_5|6|7_8|A|B):[0-9]+|ticket|prover|auditor|"
       r"preflight|dispatcher|supervisor|\bhub\b|frozen|pinned|\bpin\b|\bamend|rework|\bprobe\b|\bgate\b|\bowed\b|"
       r"\bREQ\b|\bH[0-9]{3}\b|CLAUDE\.md|HANDOVER|CONTROL|RBM[12]D/[^ ]*:[0-9]|sub-stage|successor|census")

CHECK = """/-
Release check for T{n} (dispatcher V5, {time} UTC; DECISIONS §371): a comment-only ticket must leave the
statements of the published roots unchanged (compile on `main` before and on `t/T{n}` after).
Statements only: Prop-valued `example`s whose term is the name, and `#check`; no proofs.
Run: lake env lean docs/tickets/checks/T{n}-check.lean
-/
import RBM3D

example : RBM.Univ.UNL32 →
    (RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff) ∧
      RBM.Endpoints.Thm27 := RBM.Endpoints.final_shape
example : RBM.Univ.UNL32 → RBM.Endpoints.Thm27 := RBM.Endpoints.Thm27_of_L32
example : RBM.Univ.UNL32 →
    RBM.Endpoints.decol ∧ RBM.Endpoints.locSC ∧ RBM.Endpoints.QUE ∧ RBM.Endpoints.BUniv ∧ RBM.Endpoints.QDiff :=
  RBM.Endpoints.band_terminal
example : RBM.Univ.UNL32 → RBM.BA.BAThm27L 3 := RBM.BA.baThm27L_three
#check @RBM.BA.baThm27L_any
#check @RBM.BA.baThm27L_of_ML
#check @RBM.BA.baEnd_BUnivL_of_ML
#check @RBM.Endpoints.bUniv_holds
#check @RBM.Univ.UNL32
"""

T = """Ticket: T{n} (dispatcher V5, {time} UTC; DECISIONS §355 (1), §371; precedent RBM2D §246, T2275–T2278)

Group / type: **Release clean-up, step 3: comments only, in {title}. No code change of any kind.**
**Start condition:** T2523 has merged ({h}). Start once `docs/tickets/checks/T{n}-check.lean` compiles on `main`. One of the step-3 tickets T{first}–T{last}; their file lists are disjoint from each other and from T2533 / T2534 (the block Anderson files), so any of them may run in parallel with those.
Role: `prover-hard`. Rework rate (last 10): {rw}.
Process: CLAUDE.md §4.
- Stage 1a `preflight` is **short** (no mathematics): "(i) no exponents; (ii) not applicable", verdict PASS.
- Then 1b `prover-hard`, then `auditor`.

**Goal.** GitHub will carry only the final paper and the Lean proof (DECISIONS §355). Comments and docstrings must read as documentation of finished mathematics, not as a record of how the work was organised.

**Scope.** {scope}: exactly the {nf} files listed in `docs/tickets/T{n}-files.txt` (one path per line).
At release: {nf} files, {nl} lines, about {nc} comment lines, {nh} hits of the grep below, {nr} TeX line references.

**In every file of the list, rewrite comments and docstrings (`--`, `/- -/`, `/-- -/`, `/-! -/`) so that:**
1. **No process references.** Remove:
   - ticket numbers (`T2xxx`, `T2xxxa`) in prose, `DECISIONS §…`, paper-delta numbers (`D123`, "paper-delta"), `CLAUDE.md`, `TEAM`, `HANDOVER`, `CONTROL`, instructions `H123`, `REQ`, supervisor verdicts ("supervisor 2026-10-05-1651", "1652 PASS");
   - roles (prover, auditor, preflight, repairer, dispatcher, hub, supervisor, Fable);
   - planning labels of stages and rows (`U1s2`, `U3s3a′`, `V2a`, `M/N`, `MN-D3`, `C5`, `C5L-L1`, `MA-06b`, `BA-L L3a3`, `BA-TL`, `ST-6`, `UN-01`, `KL-D1`, `PT-D1`, `EK-D1`, `LW-10c`, `X1`, `G1`–`G4` as groups, …);
   - the words ticket, gate, wave, stage, sub-stage, row (planning sense), route, amend, rework, probe, pin / pinned / frozen / freeze, landing line, stop line, census, and owed / borrowed / structural / refuted / superseded in the audit-registry sense;
   - RBM1D/RBM2D file:line references and commit hashes;
   - narration of history: "was replaced", "earlier version", "now", "no longer", "moved from", "renamed", "successor of", "the old …", "primed successor".
2. **Paper references use the final paper.** Cite labels and numbers of `paper/final/DubovaYangYauYin_RBM3D_Lean_version.pdf` (TeX in `paper/final/tex/`), for example "Lemma 2.24 (`lem:main_ind`)", "(3.3) `GijGEX`", "Theorem 2.7 (`MR:decol_BA`)".
   - Never TeX line references such as `3_5:1234`, `7_8:963-966`, `1_2:653`, `B:500`.
   - Those line numbers refer to the submission TeX `paper/tex/`. Translate them with `python3 docs/claude-team/tools/texref.py --scan <files>`: for each reference it prints the enclosing labelled environment, the proof it is in, the section, and the nearest label, with final numbers from `docs/claude-team/tools/paper-labels.tsv`. Read the TeX around the line when the context is not clear.
   - The label alone or the number alone is fine; be consistent within a file.
   - Other papers are cited bibliographically (`[YY_25, Lemma 4.1]`), never by line numbers of their TeX.
3. **What stays:** the mathematical content.
   - What a definition is, what a theorem says, why a hypothesis is there, how a proof goes, which paper result it formalizes.
   - Conventions: scales, index types, normalizations, the reading of a printed statement.
   - A sentence saying that an argument follows the two-dimensional (or one-dimensional) formalization may stay, naming at most the RBM2D (RBM1D) declaration, without file:line or commit.
   - Keep the description of the one external input `UNL32` (arXiv:1609.09011v4) where it is stated.
4. Every file keeps its copyright header and starts (after the imports and options) with a short, accurate module docstring `/-! # … -/` saying what the file contains, in mathematical terms.
5. Delete comments that only carried process information. Leave no empty comment shells. English only.

**Must not change.**
- No code token: declarations, names, statements, proofs, attributes, `open` / `variable` / `namespace` / `section` / `set_option` lines, imports, string literals, whitespace inside code.
- Do not rename anything. Names containing planning words stay (`…Pins`, `…Row`, `UNClaimRowBA`, `G1Row`, `STReg5III`, primed names, …); in prose refer to them by name without telling their history.
- Do not touch files outside `docs/tickets/T{n}-files.txt`; in particular not `RBM3D/BA/Step5III*.lean`, `RBM3D/BA/UNBUniv.lean`, `RBM3D/Main/FinalShape.lean` (changed by T2533 / T2534; their comments get a ticket of their own), `RBM3D/Test/`, `RBM3D.lean`.

**Acceptance (CLAUDE.md §4, §6).**
- A comment-stripping script applied to every file of the list on `main` and on `t/T{n}` gives identical output. It must handle nested `/- … -/`, doc comments, `--` to end of line, string and character literals. Paste the script and its summary (`identical: N files`, `different: 0`).
- `grep -rnEi '{pat}' $(cat docs/tickets/T{n}-files.txt)` on the branch prints nothing, or each remaining hit is listed with the reason it is mathematical or part of a Lean name.
- `grep -rnP '[\\x{{4e00}}-\\x{{9fff}}]' $(cat docs/tickets/T{n}-files.txt)` prints nothing.
- Every file of the list has a module docstring: paste `grep -L '/-!' $(cat docs/tickets/T{n}-files.txt)` (empty).
- Full `lake build` OK (the merge reruns it); `docs/tickets/checks/T{n}-check.lean` compiles.
- Prove report ≤ 120 lines apart from the script and its output; line 1 `Prover model: <id>`.
- No paper-delta candidates are expected. A mathematical problem noticed while reading goes in the report as an observation, never into the code.

Sole writable files: the files listed in `docs/tickets/T{n}-files.txt` (comments only), `docs/reports/T{n}-*.md`. Branch `t/T{n}`.
Required reading (only these): `CLAUDE.md` §3–§6; this ticket; `docs/tickets/T{n}-files.txt`; `docs/tickets/checks/T{n}-check.lean`; `docs/DECISIONS.md` §355, §371; the docstring of `docs/claude-team/tools/texref.py`; `paper/final/tex/` and `paper/tex/` (read-only, for labels).
Merge: rule (A); the diff touches comments only.
"""

for s in scopes:
    n = s['n']
    txt = T.format(n=n, time=TIME, h=H, first=first, last=last, rw=RW, title=s['title'], scope=s['scope'],
                   nf=s['nf'], nl=s['nl'], nc=s['nc'], nh=s['nh'], nr=s['nr'], pat=PAT,
                   )
    open(os.path.join(out, f'T{n}.md'), 'w').write(txt)
    open(os.path.join(out, 'checks', f'T{n}-check.lean'), 'w').write(CHECK.format(n=n, time=TIME))
    open(os.path.join(out, f'T{n}-files.txt'), 'w').write('\n'.join(s['files']) + '\n')
print('ok', len(scopes))
