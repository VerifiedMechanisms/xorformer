#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repository_dir="$(dirname -- "$(dirname -- "$script_dir")")"
cd "$repository_dir/formalization"

modules=(
  HeadComplexity.Atoms.AffineMonomialApproximation
  HeadComplexity.Results.MonomialStarCover
  HeadComplexity.Results.StarDegreeUpperBound
  HeadComplexity.Results.UniversalStarUpperBound
  HeadComplexity.Results.BernoulliStarCover
  HeadComplexity.Results.UniversalSublinearUpperBound
  HeadComplexity.Results.StarCoverRecursion
  HeadComplexity.Results.UniversalLinearSaving
  HeadComplexity.StarUpperBoundSubsumption
  HeadComplexity.UniversalSublinearSubsumption
  HeadComplexity.UniversalLinearSavingSubsumption
  HeadComplexity.Results.All
)

lake build "${modules[@]}"

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

# The original library modules are identical; All.lean only gains lines.
python3 - "$repository_dir" <<'PY'
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1])
baseline = '50b66da5bbcfe1d7dd98c5e403874cc5089d7e98'
paths = subprocess.check_output([
    'git', '-C', str(root), 'ls-tree', '-r', '--name-only', baseline,
    '--', 'formalization/HeadComplexity', 'formalization/HeadComplexity.lean',
], text=True).splitlines()
paths = [p for p in paths if p.endswith('.lean')]
for path in paths:
    before = subprocess.check_output(['git', '-C', str(root), 'show', f'{baseline}:{path}'])
    after = (root / path).read_bytes()
    if path == 'formalization/HeadComplexity/Results/All.lean':
        remaining = iter(after.splitlines())
        for line in before.splitlines():
            if not any(candidate == line for candidate in remaining):
                raise SystemExit(f'Original umbrella line removed or changed: {line!r}')
    elif before != after:
        raise SystemExit(f'Pre-existing Lean source changed: {path}')
print(f'Preserved {len(paths)} baseline Lean sources; All.lean only gains imports and aliases.')
PY

report_dir="$(mktemp -d)"
trap 'rm -rf "$report_dir"' EXIT
comparison_modules=(
  HeadComplexity.StarUpperBoundSubsumption
  HeadComplexity.UniversalSublinearSubsumption
  HeadComplexity.UniversalLinearSavingSubsumption
)
expected_counts=(3 3 2)
for i in "${!comparison_modules[@]}"; do
  comparison_module="${comparison_modules[$i]}"
  report_path="$report_dir/$i.log"
  lake env lean "${comparison_module//./\/}.lean" > "$report_path"
  comparison_count="$(rg -c '^COMPONENT-WISE RESULT: source strictly subsumes target under this alignment$' "$report_path")"
  if [ "$comparison_count" -ne "${expected_counts[$i]}" ]; then
    cat "$report_path" >&2
    echo "Unexpected comparison count for $comparison_module" >&2
    exit 1
  fi
  echo "$comparison_module: $comparison_count strict comparisons; requirements PROVED/PROVED; guarantees PROVED/REFUTED."
done

echo 'All eight strict comparisons passed with checked model bridges and the standard axiom allowlist.'
