# Supervisor verdicts (written only by the supervisor scheduled task)

One file per run: `docs/supervisor/YYYY-MM-DD-HHMM.md`. The file name is in UTC; it is the sort key that the dispatcher's heartbeat and the 24-hour check read. It contains:
- **trigger:** `REQ-…` (event) or daily backstop;
- **inputs read:** `docs/ROUTES.md`, plus the new tickets and reports since the previous verdict, plus any Lean or paper sources opened;
- **verdict:** PASS | RECOMMEND HOLD | RECOMMEND STOP;
- **for HOLD/STOP:** checkable sources, the exact mathematical gap, the earliest time it was visible, and the tickets dispatched after that;
- **answers** to each question in the request, numbered as in the request;
- **route budget:** per gate, the wide ticket count including rework. Flag at 25 and 40; recommend HOLD at about 50 without closure.

After handling a request, change its first line to `status: done → <verdict file name>`.

Anything written for Jun, such as a push notification, uses Los Angeles time. Repository files keep UTC.
