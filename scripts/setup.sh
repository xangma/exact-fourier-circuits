#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
mkdir -p logs outputs
if ! command -v elan >/dev/null 2>&1; then
  installer="$(mktemp -t exact-fourier-elan.XXXXXX)"
  trap 'rm -f "$installer"' EXIT
  curl --fail --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$installer"
  sh "$installer" -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi
toolchain="$(cat lean/lean-toolchain)"
elan toolchain install "$toolchain"
python3 -m venv .venv
.venv/bin/python -m pip install -e .
./scripts/verify-lean.sh
./scripts/verify-projection.sh
./scripts/verify-construction.sh
.venv/bin/python -m unittest discover -s tests
