#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1 && [[ -x ../.elan/bin/lake ]]; then
  export ELAN_HOME="$(cd ../.elan && pwd)"
  export PATH="$ELAN_HOME/bin:$PATH"
fi
lake build
python3 scripts/check_sources.py
lake env lean Audit.lean | python3 scripts/check_axioms.py
