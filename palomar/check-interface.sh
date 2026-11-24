#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
case "$(cat lean-toolchain)" in
  leanprover/lean4:v4.28.0) ;;
  *) echo "This compatibility check uses the original Lean 4.28.0 project." >&2; exit 1 ;;
esac
if ! command -v lake >/dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
  PATH="$HOME/.elan/bin:$PATH"
  export PATH
fi
lake build TransportOkaGrauert.GermStein
stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
cp palomar/Challenge.lean palomar/RegistryDefinitions.lean "$stage/"
# The verified 4.28 library predates the module system. Only the temporary
# Solution needs legacy header syntax to import it. The proof body is verbatim.
sed -e '/^module$/d' -e 's/^public import /import /' -e '/^public section$/d' \
  palomar/Solution.lean > "$stage/Solution.lean"
LEAN_PATH="$stage${LEAN_PATH:+:$LEAN_PATH}"
export LEAN_PATH
for name in Challenge RegistryDefinitions Solution; do
  lake env lean -R "$stage" -o "$stage/$name.olean" "$stage/$name.lean"
done
lake env lean --run palomar/CheckInterface.lean
