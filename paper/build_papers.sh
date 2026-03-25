#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

compile_one () {
  local tex="$1"
  echo "==> Building ${tex}"
  latexmk -pdf -interaction=nonstopmode -halt-on-error "${tex}"
}

if [[ $# -gt 0 ]]; then
  for f in "$@"; do
    compile_one "$f"
  done
else
  compile_one "Program_Notes.tex"
fi
