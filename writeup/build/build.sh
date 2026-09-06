#!/bin/bash
# Build the writeup PDF and publish it one level up. Run from this directory.
set -e
cd "$(dirname "$0")"

# pdflatex is silenced to keep the build quiet, but a LaTeX error would then
# print nothing at all and leave the previous ../neurips_2026.pdf in place
# looking current. Surface the error block instead; the memory dump after it
# is noise.
run_latex() {
  if ! pdflatex -interaction=nonstopmode -halt-on-error neurips_2026.tex > /dev/null; then
    awk '/^!/ {show=1} /^Here is how much/ {show=0} show' neurips_2026.log >&2
    exit 1
  fi
}
run_latex
if grep -q '\\bibdata' neurips_2026.aux; then
  if ! bibtex neurips_2026 > /dev/null; then
    tail -n 40 neurips_2026.blg >&2
    exit 1
  fi
fi
run_latex
run_latex
rm -f neurips_2026.aux neurips_2026.bbl neurips_2026.blg \
  neurips_2026.log neurips_2026.out neurips_2026.toc
# cp keeps ../neurips_2026.pdf's inode so PDF viewers watching the file
# refresh; mv would swap the inode out from under them.
cp neurips_2026.pdf ../neurips_2026.pdf
rm neurips_2026.pdf
if command -v pdfinfo > /dev/null 2>&1; then
  echo "Published: ../neurips_2026.pdf ($(pdfinfo ../neurips_2026.pdf | awk '/^Pages:/ {print $2}') pages)"
else
  echo "Published: ../neurips_2026.pdf"
fi
