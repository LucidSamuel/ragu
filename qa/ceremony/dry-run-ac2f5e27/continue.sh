#!/usr/bin/env bash
# Continue this QA record using the shared example procedure.
set -euo pipefail
RECORD="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec "$RECORD/../continue.sh" "$RECORD" "$@"
