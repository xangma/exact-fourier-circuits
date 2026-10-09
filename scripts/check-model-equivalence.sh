#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root/lean"
if [[ $# -ne 1 ]]; then
  printf 'Usage: %s MODULE (or upstream/RAM, upstream/Goal)\n' "$0" >&2
  exit 2
fi
module="$1"
case "$module" in
  upstream/RAM|upstream/Goal)
    name="OAI/Computability/FourierTransform/${module#upstream/}"
    source="ModelEquivalenceUpstream/$name.lean"
    package_root="ModelEquivalenceUpstream"
    ;;
  OAI.Computability.FourierCircuit.Core|UniformMachine|ModelEquivalence*)
    name="${module//./\/}"
    source="$name.lean"
    package_root="."
    ;;
  *) printf 'Unexpected module: %s\n' "$module" >&2; exit 2 ;;
esac
out=".lake/build/lib/lean/$name.olean"
mkdir -p "$(dirname "$out")"
exec lake env lean -R "$package_root" -o "$out" "$source"
