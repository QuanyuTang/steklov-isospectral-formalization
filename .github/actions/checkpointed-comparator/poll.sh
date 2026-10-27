#!/usr/bin/env bash
set -Eeuo pipefail
steklov_poll_deadline=$((SECONDS + 1200))
while [[ ! -f verification/current-ci/required-replay.exit ]]; do
  steklov_worker_pid=$(cat verification/current-ci/required-replay.pid)
  if ! kill -0 "$steklov_worker_pid" 2>/dev/null; then
    sleep 1
    if [[ ! -f verification/current-ci/required-replay.exit ]]; then
      echo 'Replay worker disappeared without an exit result; no acceptance claimed.' >&2
      exit 1
    fi
  fi
  if (( SECONDS >= steklov_poll_deadline )); then
    echo 'complete=false' >> "$GITHUB_OUTPUT"
    exit 0
  fi
  date -u '+waiting_for_required_replay=%Y-%m-%dT%H:%M:%SZ'
  tail -n 3 verification/current-ci/replay-resources.log 2>/dev/null || true
  sleep 30
done
echo 'complete=true' >> "$GITHUB_OUTPUT"
echo 'STEKLOV_REPLAY_COMPLETE=true' >> "$GITHUB_ENV"
