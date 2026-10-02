# RBM3D — rules for the Claude Code execution side (team mode, 2026-10-02)

Project: a Lean 4 + Mathlib formalization of *Delocalization of non-mean-field random matrices in dimensions d ≥ 3* (Dubova, F. Yang, H.-T. Yau, J. Yin; arXiv:2507.20274, Inventiones submission). Sister projects: `../RBM1D` (d = 1, arXiv:2501.01718, complete) and `../RBM2D` (d = 2, arXiv:2503.07606, complete: all five main theorems proved, one authorized external input). Their team system is copied here; their mathematics is not (see §5).

Who reads this file: the **execution hub** (one long-running Claude Code session on Jun's Mac) and the **subagents it starts** (`preflight`, `preflight-opus`, `prover`, `prover-hard`, `prover-opus`, `repairer`, `auditor`, defined in `.claude/agents/`). The **dispatcher** (a Cowork session) and the **supervisor** (a Cowork scheduled task) follow `docs/claude-team/TEAM.md`.
- Startup: `docs/claude-team/STARTUP.md`.
- Effective decisions: `docs/DECISIONS.md`.
- Mathematical roadmap: `docs/PLAN.md`.
- The previous work mode (one coordinator plus `docs/TASKS.md`/`docs/QUEUE.md`, until 2026-09-22) is archived in `docs/archive/2026-10-02-old-workmode/`. Search it only when you need something specific.

Write code, reports and commit messages in English. Work silently: no narration, one final result per task.

## 1. File ownership (one writer per file)

| Path | Writer |
|---|---|
| `docs/STATUS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `docs/HANDOFF.md`, `docs/ROUTES.md`, `docs/rework-ledger.md`, `docs/paper-deltas.md` (numbering), `docs/queue/CONTROL.md`, `docs/tickets/*`, `docs/claude-team/*` | dispatcher only |
| `docs/queue/T####.state`, `docs/queue/HUB.alive`, merges into `main`, root imports in `RBM3D.lean` | execution hub only |
| the ticket's "sole writable files" in its worktree, `docs/reports/T####-prove.md` | that ticket's `preflight` (section (a) only), then `prover` / `prover-hard` / `prover-opus` / `repairer` |
| `docs/reports/T####-audit.md` | that ticket's `auditor` |
| `docs/supervisor/*` (except `requests/REQ-*.md`, which the dispatcher writes) | supervisor only |
| `blueprint/src/content.tex` | only a ticket that names it as a sole writable file (a "blueprint sync" ticket); never two such tickets at once |

The dispatcher's check files `docs/tickets/checks/T####-check.lean` (§4 step 0) are the only Lean the dispatcher writes: pinned statement text, `#check` lines and `example`s that elaborate them; no proofs, no `sorry`; never imported, built into the library or merged (Jun, 2026-09-29; DECISIONS §68).

Never edit: another ticket's files or reports, `docs/archive/`, `paper/`, and **anything under `../RBM1D` or `../RBM2D`** (read-only for every RBM3D role: never write, move, build, or run a git write command there; see §5.2). For `docs/paper-deltas.md`, a ticket only proposes new entries in its report, with a temporary tag `T####a`; the dispatcher appends them and assigns the numbers.

## 2. Execution hub: one loop iteration

0. Overwrite `docs/queue/HUB.alive` with the current UTC time from `date -u`.
1. Read `docs/queue/CONTROL.md`.
   - `mode: STOP`: start nothing, and stop running workflows before their next stage.
   - `mode: HOLD`: start no new stage 1; audits of finished provers may continue.
   - `mode: AUDIT_FIRST`: start audit stages only.
   - `mode: RUN`: normal operation.
   - Execute every **Approved instruction** that has no `done:` line, then append `done: <date -u time> — <result>` under it. The `done:` lines are the only thing the hub writes in CONTROL.md.
2. For each ticket in CONTROL's **Released tickets** list that has no `docs/queue/T####.state`, and whose start condition holds (mode permitting):
   - Write the state file with `state: claimed`.
   - Create branch `t/T####` and worktree `../RBM3D-wt/T####` from `main`. Give it the build cache without sharing writable files:

     ```
     mkdir ../RBM3D-wt/T####/.lake
     ln -s "$PWD/.lake/packages" ../RBM3D-wt/T####/.lake/packages
     cp -c -R .lake/build ../RBM3D-wt/T####/.lake/build
     ```

     `cp -c` makes an APFS copy-on-write clone. Never hard-link with `cp -al`, and never share a worktree between tickets.
   - Tickets, reports, state files and CONTROL live only in the main worktree (`~/Lean_proof/RBM3D`). Give every subagent absolute paths to the ticket file, the main worktree's `docs/reports/`, and its own worktree.
   - Start **one workflow per ticket**, in the gated shape of §4. Pass the ticket and paths; add nothing, remove nothing.
3. Keep `T####.state` current as each stage finishes: `claimed | proving | preflight-fail | built | auditing | audit-pass | audit-fail | blocked | merged | held`, with one reason line, an `updated:` time from `date -u`, and the report paths. If the ticket does not specify something, set `blocked` with the question. Do not decide it yourself.
4. On `audit-pass`, merge in the same iteration (§3). Otherwise never commit to `main` except under an Approved instruction.
5. If nothing changed since the last iteration, only update `HUB.alive` and print nothing.

## 3. Standing hub rules

These are in force from the start. The dispatcher may add more in CONTROL.

- **(A) Auto-merge on audit PASS.** When a released ticket reaches `audit-pass`:
  1. Line 1 of the audit report must be `Auditor model: claude-opus-5-5`. Otherwise re-audit with the pinned auditor first.
  2. `git diff main...t/T####` must touch only the ticket's sole writable files. Otherwise set `blocked` with the file list.
  3. Bring in exactly those files.
  4. For each new module, add `import RBM3D.<Module>` after the **last `import` line** of `RBM3D.lean`. Never append at the end of the file: `#assert_rbm_axioms` must stay last.
  5. Run `lake build` (the whole library, which runs `#assert_rbm_axioms`). On any error, set `blocked` and do not commit.
  6. Commit exactly the ticket's files, `RBM3D.lean` if it changed, the state file, and the prove and audit reports, with message `T####: merge <title>`.
  7. `git push origin main`: main only, never force. If the push is rejected, stop and report; do not retry or rebase.
  8. Set the state to `merged <hash>` and append one `done:` line under CONTROL's merge log.
  - Report-only tickets skip steps 3–5 but are still audited.
- **(B) One automatic repair per RETURN.** If an audit RETURNs with a concrete repair list, start one `repairer` stage (claude-opus-5-5) in the same workflow, then a fresh `auditor`. Stop and set `audit-fail` for the dispatcher in any of these cases:
  - a second RETURN on the same ticket;
  - any BLOCKED;
  - an audit that asks for dispatcher sign-off.
  - **Escalation to Opus (DECISIONS §94, Jun).** For a ticket whose stage 1b ran as `prover-max` (Sonnet, effort max): if stage 1b ends without proving every target, or the ticket reaches its second RETURN, do not stop at `audit-fail`. Rerun stage 1b once as `prover-opus` with the effort overridden to `xhigh` (Opus 5.5), on the same branch, passing the ticket, its amends and the existing reports; then a fresh `auditor`, with rule (B) applying again. Write a `done:` line when you escalate. A preflight BLOCKED is not a model failure and still goes to the dispatcher. If the Opus round also fails, set `audit-fail` for the dispatcher. A stall (no progress) is escalated by the dispatcher through CONTROL.
- **(C) Timestamps.** Every time written anywhere (state, CONTROL, reports) comes from `date -u` at the moment of writing.
- **(D) Report headers.** Line 1 of a prove report is `Prover model: <id>`; line 1 of an audit report is `Auditor model: <id>`.
- **(E) Private helpers.** A helper lemma that the ticket does not pin must be `private` or prefixed with the file stem. Pinned names stay exactly as pinned.
- **(F) Nothing undecided starts.** A ticket starts only if CONTROL lists it under Released and its start condition holds. Held or prepared tickets never start.
- **(G) Parallelism.** Run at most the number of workflows CONTROL states (default 4). Critical-path tickets go first.
- **(H) API errors.** If a stage fails on an API error (for example 529 Overloaded), rerun that stage. Never let a later stage run on the output of a failed stage.

## 4. The gated workflow (one per ticket)

Rewritten 2026-09-29 by Jun's instructions (DECISIONS §63, §68): hard tickets on Sonnet; preflight is mathematics only; audits are statement-centred; reports are script output first; tickets are checked by compiling before release.

0. **Compile check before release (by the dispatcher).** While writing a ticket, the dispatcher writes `docs/tickets/checks/T####-check.lean`: the pinned statement text copied from its source, `#check` of every upstream declaration the ticket names, and `#check` of the downstream pin the targets must fit. The dispatcher lists it under CONTROL's **Pre-release checks**; the hub compiles each listed file with `lake env lean docs/tickets/checks/T####-check.lean` in the main worktree and writes the exit code and the error lines (script output) as a `done:` line there (the dispatcher's machine has no Lean toolchain). The dispatcher reads the result, fixes the ticket or the check, and moves the ticket to **Released** only after a clean compile. A ticket under Pre-release checks never starts.
1. **Stage 1a, agent `preflight` (Sonnet), for every role.** Mathematics only. It writes section `(a) Math preflight` of `docs/reports/T####-prove.md` with exactly two parts:
   - (i) **the exponent table**: every exponent, threshold and constant the targets depend on, its value, the constraint it must satisfy, and the slack;
   - (ii) **one concrete nondegenerate instance** (numbers) at which every hypothesis of every target holds at once, checked by a short script whose command and output are pasted.
   - Targets are restated in mathematics only as far as (i)–(ii) need. No Step 0 pastes, no name or Mathlib checks, no size estimates, no process narrative. Section (a) is at most 120 lines. It writes **no Lean anywhere**.
   - Structured result: section written (yes/no) and verdict PASS/FAIL/BLOCKED. Stage 1b starts only on PASS. Rerun once on API errors; otherwise set `preflight-fail`.
2. **Stage 1b**, the ticket's role: `prover` (Sonnet, effort high), `prover-hard` (Sonnet, effort xhigh), `prover-max` (the `prover-hard` agent with the per-stage effort override `max`), or `repairer`. (`prover-opus`/`preflight-opus` are not used for new first rounds: DECISIONS §63.)
   - It reads (a) and does not edit it; corrections go in `(a′) Preflight corrections` with a `date -u` time.
   - It writes Lean only in the sole writable files, builds each module with `lake build RBM3D.<Module>`, prints axioms, and commits on `t/T####`.
   - **Every endpoint theorem (each target theorem of the ticket) gets a compiled nonempty instance** in the same file: an `example` (or a named check) that applies the theorem at concrete nondegenerate data with every hypothesis discharged. No `N = 0`, empty index set, collapsed window or `False` premise. A hypothesis that is another gate's pin not yet proved (for example `Step2LocalPT`, `GbEXPHypV3`, `KboundConcl`) may stay as a hypothesis of the example; every deterministic hypothesis is discharged at the concrete data.
3. **Stage 2 `auditor`** (a fresh agent that wrote nothing; its own detached worktree): statement-centred, as in §6.
4. Both stage-1 prompts must contain this sentence verbatim:

   > "Every fact you state in the report must come from `date -u`, the tool log, or the files; a false statement fails the audit by itself. Put evidence in the report as script output (the command and its verbatim output), not as prose, and keep the report within CLAUDE.md §6's length limits. Do not narrate edit or build histories."

## 5. Mathematical and Lean gates (all roles)

1. **Sole source:** `paper/2507.20274-inventiones-submission.pdf` (TeX in `paper/tex/`; section-to-file map in `paper/README.md`). Cite equation and label numbers.
   - Do not import proofs from other papers. Where the paper cites `[YY_25]` or other work, Lean takes it as an explicit hypothesis or a separate ticket, as `docs/DECISIONS.md` decides.
   - Any external input must be listed in DECISIONS as authorized.
2. **d ≥ 3 is not d = 1 or d = 2.** The lattice is `Z_L^d` with `d` a parameter (`3 ≤ d` only where the mathematics needs it); the propagator `Θ` has no closed form, and its decay estimates in this paper (`lem_propTH`) are partly cited from other work — DECISIONS decides which are authorized inputs and which are proved. **Porting from `../RBM2D` and `../RBM1D` is allowed and encouraged**: the three papers are parallel, and you may copy their Lean statements, proofs and helper lemmas into this ticket's sole writable files and adapt them there. Rules:
   - `../RBM1D` and `../RBM2D` are read-only: read with `cat`/`grep`/`git -C ../RBM2D --no-optional-locks …` only. Never write, move, `lake build`, or run any git write command in them, and never import their modules; copy the text.
   - Cite every port in the report: source project, file:line and commit (`git -C ../RBM2D --no-optional-locks log -1 --format=%h`).
   - Re-check every ported statement against this paper. A d = 1 or d = 2 result is not evidence for d ≥ 3: replace the dimension-specific facts (index type `ZMod L`/`Z2 L` vs `Zd d L`, closed forms of `Θ`, lattice sums and their logarithms in d = 2, the scalings of `ℓ`, `M` and block size `W^d`, `N = (W L)^d`), and redo every exponent count.
   - Names: RBM1D and RBM2D also use namespace `RBM`. Before adding a ported public name, check it does not already exist in RBM3D (`grep -rn`); unpinned helpers are `private` or prefixed with the file stem (§3 (E)).
3. **Proof hygiene.**
   - No `sorry`, `admit`, declared `axiom`, or `native_decide`.
   - `#assert_rbm_axioms` at the end of `RBM3D.lean` hard-checks the whole `RBM` namespace: only `propext`, `Classical.choice`, `Quot.sound`.
   - Never change a frozen signature; add a primed successor.
4. **Builds.** Every new module must pass `lake build RBM3D.<Module>`; `lake env lean` alone is not acceptance. Merges need the full `lake build`.
5. **Hypotheses and parameters.**
   - A new hypothesis needs a nondegenerate witness that satisfies all hypotheses at once. Avoid `N = 0`, empty index sets, collapsed windows, and witnesses that work only because a quantity is astronomically large.
   - An external hypothesis also needs a concrete limit check (TEAM §8 lesson 14).
   - Every endpoint theorem carries a compiled nonempty instance (§4 step 2).
   - Keep the paper's parameter order (fixed parameters before `∀ᶠ N`), sharp losses, and all dimensions, energies, windows and charges.
6. **Special cases.** A conditional adapter or special-case result is never the general statement. Say so in the report.
7. **Docstrings are not evidence.** Judge a declaration by the hypotheses in its signature.
8. **Mathlib names.** Do not invent them. Check with `grep -rn` in `.lake/packages/mathlib/Mathlib/` or with `#check`. Record verified names, and names verified absent, in the report; the dispatcher copies them to `docs/mathlib-api.md`.
9. **Paper deltas.** Every Lean/paper statement difference is proposed in the report as a paper-delta candidate `T####a`.
10. **Old-mode documents are unverified** (Jun, 2026-09-28 21:23 UTC; DECISIONS §11). Some of the plans and claims written before team mode are wrong Treat as leads only, never as evidence: `docs/PLAN.md`, `docs/STATUS.md`, `docs/stochastic-audit.md`, `docs/mathlib-api.md`, everything under `docs/archive/`, all existing paper-deltas entries (written before team mode), the blueprint, and docstrings/comments in merged Lean files. Any claim taken from them into a report (a lemma "is proved", a bound "holds", a counterexample, a route "works", a constant) must be re-verified against the paper TeX/PDF and the Lean signatures, with the evidence pasted. If it turns out wrong, report it as a finding and propose a correction (paper-delta or doc fix). Merged Lean statements themselves are checked by Lean; what they are *claimed* to mean is not.

## 6. Reports (script output first, bounded length)

**`docs/reports/T####-prove.md`**, at most 300 lines:
- (a) Math preflight (stage 1a): the exponent table and the concrete instance (§4 step 1).
- (a′) Corrections, if any.
- (b) Script output: the build command and the tail of its output; `#print axioms` of every target; each target's statement, extracted from the file by script; the compiled nonempty instance; the name-clash grep of new public names; for ports, RBM1D file:line and `git -C ../RBM1D --no-optional-locks diff --stat <commit> HEAD -- <files>`. Narrative at most 40 lines.
- (c) Verified Mathlib names used, one line each.
- (d) Open issues and paper-delta candidates (`T####a`, …).

**`docs/reports/T####-audit.md`**, at most 150 lines, mainly script output. Statement-centred; per target PASS / RETURN (exact defect and "Required for resubmission") / BLOCKED (exact missing input):
- the Lean statement against the ticket's pin (a script diff) or the ticket's mathematics: hypotheses, quantifier order, losses, ranges, dimensions;
- hidden hypotheses (structure fields), vacuity, circular dependencies;
- the compiled nonempty instance of every endpoint theorem: RETURN if missing or degenerate;
- `lake build RBM3D.<Module>` in the audit worktree and the printed axioms (the hub runs the full build at merge);
- paper-delta coverage of every Lean/paper statement difference.

Process forensics (transcript timestamps, replaying the edits of section (a)) are not part of the audit. A report defect that changes no statement, instance, build, axiom or paper-delta coverage is recorded as an observation, not a RETURN.

The final chat reply of any subagent is one line: ticket, verdict, report path.

## 7. Environment and style (from the project's first phase)

- **Versions and cache.** Lean `4.34.0` / Mathlib `v4.34.0`, pinned by `lean-toolchain` and `lake-manifest.json`. Before the first build, run `lake exe cache get`.
  - Offline, first check that every package commit in `lake-manifest.json` matches `../RBM2D`. Then make an independent copy with `cp -cR ../RBM2D/.lake/packages .lake/packages`.
  - Never make a writable symlink into a sister project's package tree.
- **Namespace and index type.**
  - The namespace is `RBM`, the same name as in RBM1D and RBM2D. The projects are never imported together.
  - The lattice index is `RBM.Zd d L := Fin d → ZMod L`, with `d` a parameter.
  - The paper's `|x|_L` is the periodic distance defined in `RBM3D/Defs/Lattice.lean` (check its definition before use).
- **Variable conventions:** `d L : ℕ`, `hd : 3 ≤ d` only where needed, `hL : 3 ≤ L`, spectral parameters `ξ ζ : ℂ` with `‖ξ‖ < 1`.
- **Constants** need not be optimal. Hard-code them; do not write `∃ C`.
- **Copyright header:** copy it from an existing file.
- **Git.**
  - Stage files only by name. Never `git add -A`, `git add .`, `git reset --hard`, `git clean`, or `rm -rf`.
  - Commit identity: `Jun Yin <321276894+JYin80@users.noreply.github.com>`, from the local `.git/config`. Do not override it.
- **Blueprint and CI.**
  - Blueprint nodes (`\lean{}`, `\leanok`) are updated only by blueprint-sync tickets.
  - CI publishes only on push.
