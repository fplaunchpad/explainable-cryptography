#!/usr/bin/env bash
# Build one document and check its links to the formal evidence.
set -euo pipefail
cd "$(dirname "$0")/.."
document=reference
if [[ $# -gt 0 ]]; then
  if [[ $# -ne 2 || "$1" != --document || ( "$2" != reference && "$2" != catalogue ) ]]; then
    echo "Usage: $0 [--document reference|catalogue]" >&2
    exit 2
  fi
  document="$2"
fi
log_dir="tmp/formal-reference/$document"
mkdir -p "$log_dir"
if [[ "$document" == reference ]]; then
  stem=main
  lake build > "$log_dir/lake-build.log" 2>&1
  python3 scripts/check_helios_claims.py --build-log "$log_dir/lake-build.log"
else
  stem=catalogue
  lake build HeliosExecution > "$log_dir/lake-build.log" 2>&1
fi
python3 scripts/check-formal-reference.py --document "$document"
PYTHONDONTWRITEBYTECODE=1 python3 scripts/test-formal-reference.py --document "$document"
pdf_source="docs/formal-reference/$stem.tex"
pdf_output="docs/formal-reference/$stem.pdf"
pdf_log="$log_dir/pdf-build.log"
# Compilation is self-contained so public CI does not need access to the research
# skills checkout. Research and visual-review requirements still apply locally.
compile_pdf() {
  if command -v tectonic >/dev/null 2>&1; then
    (cd docs/formal-reference && tectonic -X compile "$stem.tex" --outdir .)
  elif command -v latexmk >/dev/null 2>&1; then
    (cd docs/formal-reference && latexmk -xelatex -interaction=nonstopmode "$stem.tex")
  else
    echo 'Install tectonic or latexmk to build the reference PDF' >&2
    return 1
  fi
}
if ! compile_pdf > "$pdf_log" 2>&1; then
  cat "$pdf_log"
  exit 1
fi
# Some Tectonic/macOS failures can report exit status zero. Check diagnostics too.
if rg -n 'panicked|(^|[[:space:]])error:|Overfull|Missing character|could not represent character|undefined references|undefined citation' "$pdf_log"; then
  exit 1
fi
test -s "$pdf_output"
test "$pdf_output" -nt "$pdf_source"
pdftotext -layout "$pdf_output" "$log_dir/$stem.txt"
pdfinfo "$pdf_output" > "$log_dir/pdfinfo.txt"
if rg -n '\?\?' "$log_dir/$stem.txt"; then
  echo 'Unresolved reference marker in rendered PDF' >&2
  exit 1
fi
printf 'Built %s; inspect every rendered page before recording a new visual audit.\n' "$pdf_output"
