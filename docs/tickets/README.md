# Tickets (dispatcher only)

One file per ticket: `docs/tickets/T####.md`. RBM3D team-mode tickets start at **T2001**. The old mode's T1–T31 and S0–S9 are in `docs/archive/2026-09-28-old-workmode/TASKS.md`.

- **A ticket is never edited after it is written.** Corrections go in `T####-amend-N.md`. An amend before start is not rework; after start it is.
- A ticket starts only when CONTROL lists it under **Released** and its start condition holds.
- `QUEUE.md` holds the organized queue: released, waiting, and waiting for Jun.

## Template

(Rewritten 2026-09-29 for Jun's process, DECISIONS §63, §68: Sonnet roles, math-only preflight, statement-centred audit, script-output reports, compile check before release, medium-sized tickets.)

- Size: about 600–1500 lines. Adjacent small rows of a design table (same file or same dependency layer, each under about 500 lines) are merged into one ticket.
- While writing the ticket, write `docs/tickets/checks/T####-check.lean`, list it under CONTROL's Pre-release checks, read the hub's compile output, and move the ticket to Released only after a clean compile (CLAUDE.md §4 step 0).

```text
Ticket: T#### (dispatcher V<n>, <UTC time from date -u>; <decision or instruction that authorizes it>)
Group / type: **<gate>-<id> (<gate name>) / prove | report only (design / survey) | repair — <one-line title>.**
**Start condition: start now | after T#### and T#### have merged.** <call-level reason (TEAM §8 lessons 11, 13)>
Role: `prover` | `prover-hard` | `prover-max`. Why (TEAM §1, DECISIONS §63): <pinned small ticket / longer but bounded / interface, own route, exponent control, critical-path terminal>.
Process: CLAUDE.md §4 (step 0 check file `docs/tickets/checks/T####-check.lean` → stage 1a `preflight` → stage 1b role → stage 2 `auditor`).

**Targets** (namespace, new file path): <pinned statement(s) copied from the named source, or the statement in mathematics with its exact hypotheses>.
- Route, step by step (sources: paper labels, RBM1D file:line at commit, merged declarations).
- If <a check fails>, stop and report. Do not change the pin.

**Preflight (mathematics only)**: exponent-table rows: <the exponents/constants and constraints to tabulate>; instance: <the concrete data to use>.

**Instance to compile in the same file**: for each target theorem, an `example` at <concrete nondegenerate data> with every hypothesis discharged.

Sole writable files: `RBM3D/<Path>.lean` (new). Branch t/T####. Root import: added by the hub at merge.
Required reading (only these): `CLAUDE.md` §4–§6; this ticket; <specific paper labels, report sections, files>.
Acceptance criteria (CLAUDE.md §6):
- `lake build RBM3D.<Module>`; axioms standard; no `sorry`/`admit`/`axiom`/`native_decide`; `git diff` touches only the sole writable files;
- each target statement equals its pin (script diff) or the ticket's mathematics, with no added hypothesis (added ones are candidates `T####a`, …);
- a compiled nonempty instance for every target theorem;
- RBM1D ports cited (file:line, commit) with the `git diff --stat` line;
- prove report ≤ 300 lines, script output first; paper-delta candidates listed.
```
