#!/bin/sh
# Run from any directory with the pinned Lean toolchain available through elan.
set -eu
if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
  PATH="$HOME/.elan/bin:$PATH"
  export PATH
fi
cd "$(dirname "$0")/.."
lake build
lake env lean CheckStrictExhaustion.lean
lake env lean Audit.lean
lake env lean ReplayProject.lean
lake env lean CheckGeneralStein.lean
