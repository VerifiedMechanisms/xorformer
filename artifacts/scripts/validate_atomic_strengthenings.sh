#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH='' cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repository_dir="$(dirname -- "$(dirname -- "$script_dir")")"
cd "$repository_dir/formalization"

modules=(
  HeadComplexity.Atoms.AtomicSampling
  HeadComplexity.Results.AtomicMarginEntropy
  HeadComplexity.Results.AtomicMarginProfile
  HeadComplexity.Results.AtomicMarginRange
  HeadComplexity.Results.AtomicConditionGap
  HeadComplexity.AtomicEntropySubsumption
  HeadComplexity.AtomicProfileSubsumption
  HeadComplexity.AtomicRangeSubsumption
  HeadComplexity.AtomicConditionGapSubsumption
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
