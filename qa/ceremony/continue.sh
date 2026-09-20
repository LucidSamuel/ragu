#!/usr/bin/env bash
# QA example for the temporary registry-tag workaround.
# Usage: continue.sh <record-directory> [beacon-height]
#
# The default uses the verified timestamp height + 100. An explicit height
# exercises a dry run without that ordering guarantee.
set -euo pipefail
if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo "usage: continue.sh <record-directory> [beacon-height]" >&2
  exit 2
fi
cd "$1"
shift
REPO="$(git rev-parse --show-toplevel)"
MANIFEST_DIGEST="$(shasum -a 256 setup.manifest | cut -d ' ' -f 1)"
if [ "$MANIFEST_DIGEST" != "$(cat manifest_digest.txt)" ]; then
  echo "setup.manifest does not match manifest_digest.txt; prepare a fresh record." >&2
  exit 1
fi

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

echo "== 1. stamp, upgrade, and verify the manifest =="
if [ ! -f setup.manifest.ots ]; then
  "$OTS" stamp setup.manifest
fi

"$OTS" upgrade setup.manifest.ots || true
N=""
if VERIFIED="$("$OTS" verify setup.manifest.ots 2>&1)"; then
  printf '%s\n' "$VERIFIED"
  # Use only the height ots verified against Bitcoin, not unverified metadata
  # from `ots info`. ots verifies the file digest and the earliest valid proof.
  N="$(printf '%s\n' "$VERIFIED" | sed -n \
    's/^Success! Bitcoin block \([0-9][0-9]*\) attests existence as of .*$/\1/p')"
  if [[ ! "$N" =~ ^[0-9]+$ ]]; then
    echo "cannot identify a single verified Bitcoin attestation height." >&2
    exit 1
  fi
  echo "verified attestation in block N=$N"
else
  printf '%s\n' "$VERIFIED" >&2
  if [ $# -eq 0 ]; then
    echo "cannot choose N+100 without a verified timestamp; ots verify requires Bitcoin Core." >&2
    exit 1
  fi
  echo "dry run: the timestamp is unverified."
fi

echo "== 2. choose the beacon block =="
if [ $# -ge 1 ]; then
  BEACON_HEIGHT="$1"
  RULE="given"
  echo "using block $BEACON_HEIGHT as given (dry run: not tied to the attestation)"
else
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

# Keep the existing records intact if derivation fails, including when cargo
# emits partial output before returning an error. Stage on the same filesystem.
CEREMONY_OUTPUT="$(mktemp -d .continue.XXXXXXXX)"
trap 'rm -rf -- "$CEREMONY_OUTPUT"' EXIT
printf '%s\n' "$B1" > "$CEREMONY_OUTPUT/beacon.txt"
printf 'ATTESTATION_BLOCK=%s\nBEACON_RULE=%s\nBEACON_HEIGHT=%s\n' \
  "${N:-unverified}" "$RULE" "$BEACON_HEIGHT" > "$CEREMONY_OUTPUT/attestation.txt"

echo "== 4. derive the tags =="
(cd "$REPO" && cargo run -q -p ragu_ceremony --bin registry_tags -- "$B1" "$MANIFEST_DIGEST") \
  > "$CEREMONY_OUTPUT/tags.txt"
mv "$CEREMONY_OUTPUT/beacon.txt" "$CEREMONY_OUTPUT/attestation.txt" "$CEREMONY_OUTPUT/tags.txt" .
cat tags.txt
echo
if [ -z "$N" ]; then
  echo "Note: this dry run has no verified attestation; re-run later to upgrade and verify setup.manifest.ots."
fi
echo "Keep commit.txt, setup.manifest, manifest_digest.txt, setup.manifest.ots, attestation.txt, beacon.txt and tags.txt together."
