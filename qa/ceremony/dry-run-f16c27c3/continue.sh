#!/usr/bin/env bash
# Continues the registry-tag ceremony started for commit f16c27c3 (see
# RECORD.md).
#
#   ./continue.sh            beacon block = N + 100, N = attestation block
#   ./continue.sh <height>   beacon block = <height>, whatever the attestation
#                            state (dry runs only; the record says so)
#
# Upgrades the OpenTimestamps proof, fetches the beacon block's hash from two
# explorers, derives the tags, and writes attestation.txt, beacon.txt and
# tags.txt. Safe to re-run; exits 1 while there is still something to wait for.
set -euo pipefail
cd "$(dirname "$0")"
REPO="$(git rev-parse --show-toplevel)"
CODE_HASH="$(cat commit.txt)"

if command -v ots >/dev/null 2>&1; then
  OTS=ots
else
  VENV="${XDG_CACHE_HOME:-$HOME/.cache}/ragu-ots-venv"
  if [ ! -x "$VENV/bin/ots" ]; then
    python3 -m venv "$VENV"
    "$VENV/bin/pip" install -q opentimestamps-client
  fi
  OTS="$VENV/bin/ots"
fi

echo "== 1. upgrade the timestamp proof =="
"$OTS" upgrade commit.txt.ots || true
INFO="$("$OTS" info commit.txt.ots)"
N="$(printf '%s\n' "$INFO" | grep -o 'BitcoinBlockHeaderAttestation([0-9]*)' \
     | grep -o '[0-9]*' | sort -n | head -1 || true)"
if [ -n "$N" ]; then
  echo "attested in block N=$N"
else
  pending="$(printf '%s\n' "$INFO" | grep -c PendingAttestation || true)"
  echo "attestation pending: $pending calendar(s) not yet confirmed in Bitcoin."
fi

echo "== 2. choose the beacon block =="
if [ $# -ge 1 ]; then
  BEACON_HEIGHT="$1"
  RULE="given"
  echo "using block $BEACON_HEIGHT as given (dry run: not tied to the attestation)"
else
  if [ -z "$N" ]; then
    echo "cannot choose N+100 without the attestation. Try again in a few hours."
    exit 1
  fi
  BEACON_HEIGHT=$((N + 100))
  RULE="N+100"
fi
TIP="$(curl -sf --max-time 15 https://mempool.space/api/blocks/tip/height)"
if [ "$TIP" -lt "$BEACON_HEIGHT" ]; then
  left=$((BEACON_HEIGHT - TIP))
  echo "block $BEACON_HEIGHT not mined yet: $left block(s) to go (~$((left * 10)) min)."
  exit 1
fi

echo "== 3. beacon output from two independent explorers =="
B1="$(curl -sf --max-time 15 "https://mempool.space/api/block-height/$BEACON_HEIGHT")"
B2="$(curl -sf --max-time 15 "https://blockstream.info/api/block-height/$BEACON_HEIGHT")"
if [ "$B1" != "$B2" ]; then
  echo "explorers disagree on block $BEACON_HEIGHT: $B1 vs $B2"
  exit 1
fi
echo "B = hash of block $BEACON_HEIGHT = $B1"
printf '%s\n' "$B1" > beacon.txt
printf 'ATTESTATION_BLOCK=%s\nBEACON_RULE=%s\nBEACON_HEIGHT=%s\n' \
  "${N:-pending}" "$RULE" "$BEACON_HEIGHT" > attestation.txt

echo "== 4. derive the tags =="
(cd "$REPO" && cargo run -q -p ragu_pcd --example registry_tags -- "$B1" "$CODE_HASH") | tee tags.txt
echo
if [ -z "$N" ]; then
  echo "Note: the attestation is still pending; re-run later to upgrade commit.txt.ots."
fi
echo "Publish commit.txt, commit.txt.ots, attestation.txt, beacon.txt and tags.txt together."
