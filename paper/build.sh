#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
LATEX="${LATEX:-pdflatex}"
if [[ -n "${BIBTEX:-}" ]]; then
  bibtex_cmd="$BIBTEX"
elif command -v bibtex >/dev/null 2>&1; then
  bibtex_cmd=bibtex
elif command -v bibtex.original >/dev/null 2>&1; then
  bibtex_cmd=bibtex.original
else
  echo "BibTeX is required; install it or set BIBTEX." >&2
  exit 1
fi
run_latex() {
  "$LATEX" -interaction=nonstopmode -halt-on-error -file-line-error "$1.tex"
}
run_latex main
"$bibtex_cmd" main
run_latex main
run_latex main
if grep -E 'undefined references|undefined citations|multiply defined|Overfull' main.log; then
  echo "Unresolved reference or layout overflow in main.log." >&2
  exit 1
fi
