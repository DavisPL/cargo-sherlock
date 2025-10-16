#!/usr/bin/env bash
set -euo pipefail

# ----- Config -----
START_DATE="2025-06-01"
END_DATE="2025-08-31"

CRATE_PREFIX="supply-chain-trust-example-crate-"
START_IDX=1
END_IDX=100

OUTFILE="downloads_${START_DATE//-/}_${END_DATE//-/}.csv"

# Rate limit: wait at least this many seconds between requests
# (e.g., 0.5 = ~2 requests/sec; bump higher if needed)
BASE_SLEEP="0.5"

# Backoff settings (for 429/5xx or network hiccups)
MAX_RETRIES=6
BACKOFF_BASE=1.0   # first retry waits 1s, then 2s, 4s, ...
JITTER_MAX_MS=300  # up to 300ms random jitter on each retry

USER_AGENT="crate-downloads-summarizer/1.0 (+curl+jq)"

# ----- Functions -----

# random jitter in seconds (0..JITTER_MAX_MS)
rand_jitter() {
  python3 - "$JITTER_MAX_MS" <<'PY'
import random, sys
mx = int(sys.argv[1])
print("{:.3f}".format(random.randint(0, mx)/1000))
PY
}

# Sleep helper: base sleep plus small jitter
rate_sleep() {
  sleep "$BASE_SLEEP"
}

# Fetch URL with retries/backoff. Echoes body on success; returns non-zero on failure.
fetch_with_retries() {
  local url="$1"
  local attempt=0

  while :; do
    # capture body + status code in one go; don't use -f so we can read non-2xx
    local resp status body
    resp="$(curl -sS -H "User-Agent: ${USER_AGENT}" -w $'\n%{http_code}' "$url" || true)"
    status="${resp##*$'\n'}"
    body="${resp%$'\n'$status}"

    if [[ "$status" == "200" ]]; then
      printf '%s' "$body"
      return 0
    fi

    # Retry on 429 and 5xx; otherwise give up
    if [[ "$status" == "429" || "$status" =~ ^5[0-9][0-9]$ ]]; then
      if (( attempt >= MAX_RETRIES )); then
        echo "[warn] giving up after $MAX_RETRIES retries (status $status)" >&2
        return 1
      fi
      # exponential backoff + jitter
      sleep_time=$(python3 - <<PY
import sys, math
base = float(sys.argv[1]); att = int(sys.argv[2])
print("{:.3f}".format(base*(2**att)))
PY
"$BACKOFF_BASE" "$attempt")
      jitter="$(rand_jitter)"
      echo "[info] status $status; retrying in ${sleep_time}s + ${jitter}s..." >&2
      sleep "$sleep_time"
      sleep "$jitter"
      attempt=$((attempt+1))
      continue
    else
      echo "[warn] non-retryable status $status" >&2
      return 1
    fi
  done
}

sum_downloads_in_range() {
  local crate="$1"
  local start="$2"
  local end="$3"
  local url="https://crates.io/api/v1/crates/${crate}/downloads"

  if ! json="$(fetch_with_retries "$url")"; then
    echo 0
    return 0
  fi

  # Sum downloads for dates in [start, end]
  # If none, return 0
  printf '%s' "$json" \
    | jq --arg start "$start" --arg end "$end" '
        [ .version_downloads[]?
          | select(.date >= $start and .date <= $end)
          | .downloads
        ] | add // 0
      '
}

# ----- Main -----
echo "crate,total_downloads" > "$OUTFILE"

for n in $(seq "$START_IDX" "$END_IDX"); do
  id=$(printf "%06d" "$n")
  crate="${CRATE_PREFIX}${id}"

  total="$(sum_downloads_in_range "$crate" "$START_DATE" "$END_DATE" || echo 0)"
  # coerce to integer if jq/curl glitched
  if ! [[ "$total" =~ ^[0-9]+$ ]]; then total=0; fi

  echo "${crate},${total}" >> "$OUTFILE"
  echo "done: ${crate} -> ${total}"

  # polite rate limiting between calls
  rate_sleep
done

echo "Saved to $OUTFILE"
