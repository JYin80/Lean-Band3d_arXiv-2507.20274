# Supervisor request queue

- The dispatcher writes `REQ-YYYY-MM-DD-HHMM.md` (UTC, from `date -u`). Line 1 is exactly `status: open`.
- The supervisor task runs every hour. It handles every open request, oldest first, writes a verdict file in `docs/supervisor/`, and changes line 1 to `status: done → <verdict file name>`.
- A request states:
  - the event;
  - the counts (gate, wide count);
  - numbered questions;
  - the files to read.

  It says whether anything is blocked while waiting. Usually nothing is: dispatching continues unless the question could make running tickets useless.
