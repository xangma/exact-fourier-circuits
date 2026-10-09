#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root/lean"
if [[ $# -ne 1 || ! "$1" =~ ^DFTModel[A-Za-z0-9_.]*$ ]]; then
  printf 'Usage: %s DFTModelMODULE\n' "$0" >&2
  exit 2
fi
name="${1//./\/}"
out=".lake/build/lib/lean/$name.olean"
mkdir -p "$(dirname "$out")"
exec lake env lean -o "$out" "$name.lean"
