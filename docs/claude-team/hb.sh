#!/bin/bash
# Dispatcher idle-heartbeat signature for RBM3D (run on the Cowork device shell).
# Prints the diff against the previous run and then saves the new signature.
# NOCHANGE means nothing to do this heartbeat.
cd "$HOME/mnt/RBM3D" || exit 1
sig() {
  # HUB.alive changes every hub loop; report only ok/STALE so an idle hub gives NOCHANGE (V2, 2026-10-01)
  a=$(date -u -d "$(cat docs/queue/HUB.alive 2>/dev/null)" +%s 2>/dev/null || echo 0)
  if [ $(( $(date -u +%s) - a )) -le 900 ]; then echo "alive: ok"; else echo "alive: STALE $(cat docs/queue/HUB.alive 2>/dev/null)"; fi
  echo "drained: $(ls -l --time-style=+%FT%T docs/queue/DRAINED 2>/dev/null | awk '{print $6}')"
  ls -l --time-style=+%FT%T docs/queue/*.state 2>/dev/null | awk '{print "state:",$6,$7}'
  ls -lt --time-style=+%FT%T docs/reports 2>/dev/null | sed -n 2,6p | awk '{print "report:",$6,$7}'
  ls -lt --time-style=+%FT%T docs/supervisor 2>/dev/null | sed -n 2,4p | awk '{print "sup:",$6,$7}'
  head -qn1 docs/supervisor/requests/REQ-*.md 2>/dev/null | grep -c 'status: open' | sed 's/^/open-req: /'
  echo "control: $(ls -l --time-style=+%FT%T docs/queue/CONTROL.md | awk '{print $6}')"
}
sig > "$HOME/hb3d_now.txt"
echo "now: $(date -u +%FT%TZ)"
if [ -f "$HOME/hb3d_last.txt" ]; then diff "$HOME/hb3d_last.txt" "$HOME/hb3d_now.txt" && echo NOCHANGE; else echo FIRST; fi
cp "$HOME/hb3d_now.txt" "$HOME/hb3d_last.txt"
