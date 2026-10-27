#!/usr/bin/env bash
set -Eeuo pipefail
mkdir -p verification/current-ci
(
  while true; do
    {
      date -u '+resource_snapshot=%Y-%m-%dT%H:%M:%SZ'
      free -m
      ps -C leanchecker,nanoda_bin,con-ron,lake -o pid,comm,etime,pcpu,pmem,rss --no-headers || true
      df -h .
    } >> verification/current-ci/replay-resources.log
    sleep 60
  done
) &
steklov_monitor_pid=$!
trap 'kill "$steklov_monitor_pid" 2>/dev/null || true' EXIT
set +e
/usr/bin/time -v nice -n 10 bash scripts/verify-required-comparator.sh > verification/current-ci/comparator-required.log 2>&1
steklov_replay_exit=$?
set -e
printf '%s\n' "$steklov_replay_exit" > verification/current-ci/required-replay.exit.tmp
mv verification/current-ci/required-replay.exit.tmp verification/current-ci/required-replay.exit
exit "$steklov_replay_exit"
