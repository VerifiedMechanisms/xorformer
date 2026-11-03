#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repository_dir="$(dirname -- "$(dirname -- "$script_dir")")"
cd "$repository_dir/formalization"

modules=(
  HeadComplexity.BooleanCube.BinaryEncoding
  HeadComplexity.Polynomial.AffineSubstitution
  HeadComplexity.Polynomial.RationalStrictWitness
  HeadComplexity.Results.Addressing
  HeadComplexity.Results.AddressingCertificates
  HeadComplexity.Results.AffineZeroSetInterpolation
  HeadComplexity.Results.OpenNeighborhoodCover
  HeadComplexity.Results.SyndromeCover
  HeadComplexity.Results.SyndromeLift
  HeadComplexity.Results.SyndromeCoverCertificates
  HeadComplexity.Results.UniversalNeighborhoodBound
  HeadComplexity.Results.FixedDenominatorInterpolation
  HeadComplexity.Results.RestrictedCounting
  HeadComplexity.Results.FixedDegreeCounting
  HeadComplexity.Results.SharedWidthNormalForm
  HeadComplexity.AutomlrSubsumption
  HeadComplexity.Results.All
)

lake --wfail build "${modules[@]}"

sources=()
for module_name in "${modules[@]}"; do
  sources+=("${module_name//./\/}.lean")
done
if rg -n 'sorry|admit\b' -- "${sources[@]}"; then
  echo 'Proof placeholders are not allowed.' >&2
  exit 1
else
  scan_status=$?
  if [ "$scan_status" -ne 1 ]; then
    exit "$scan_status"
  fi
fi

lake env lean --run "$script_dir/AxiomCheck.lean" "${modules[@]}"

report_path="$(mktemp)"
trap 'rm -f "$report_path"' EXIT
lake env lean HeadComplexity/AutomlrSubsumption.lean > "$report_path"
comparison_count="$(rg -c '^COMPONENT-WISE RESULT: source strictly subsumes target under this alignment$' "$report_path")"
if [ "$comparison_count" -ne 5 ]; then
  cat "$report_path" >&2
  echo 'Expected five strict comparisons.' >&2
  exit 1
fi
echo 'Five strict comparisons: requirements PROVED/PROVED; guarantees PROVED/REFUTED.'

python3 "$repository_dir/artifacts/calculations/verify_automlr_constructions.py"
python3 "$repository_dir/artifacts/calculations/verify_four_bit_covector_classification.py"

python3 - "$repository_dir" <<'PY'
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1])
baseline = 'f4781ed'
paths = subprocess.check_output([
    'git', '-C', str(root), 'ls-tree', '-r', '--name-only', baseline,
    '--', 'formalization/HeadComplexity', 'formalization/HeadComplexity.lean',
], text=True).splitlines()
for path in (p for p in paths if p.endswith('.lean')):
    before = subprocess.check_output(['git', '-C', str(root), 'show', f'{baseline}:{path}'])
    after = (root / path).read_bytes()
    if path.endswith('/Results/All.lean'):
        remaining = iter(after.splitlines())
        for line in before.splitlines():
            if not any(candidate == line for candidate in remaining):
                raise SystemExit(f'Original umbrella line changed: {line!r}')
    elif before != after:
        raise SystemExit(f'Pre-existing Lean source changed: {path}')
print('Pre-existing Lean sources preserved; the result umbrella only gains imports and aliases.')
PY

echo 'Automlr integration validation passed.'
