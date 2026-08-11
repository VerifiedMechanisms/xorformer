#!/bin/bash
#SBATCH --job-name=lean-build
#SBATCH --account=gusr38169
# cbuild is the official build partition (has internet, for refreshing elan/cache);
# staging is the same srv hardware as a fallback (officially data-transfer, but works).
# SLURM schedules on whichever is free first. Both bill 2.0 SBU/thread-hour.
#SBATCH --partition=cbuild,staging
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=32G
#SBATCH --time=00:25:00
#SBATCH --output=/gpfs/work5/0/gusr0688/fair_stuff/how-many-attention-heads-xor/head-complexity/build.slurm.out

set -uo pipefail
export ELAN_HOME=/gpfs/work5/0/gusr0688/fair_stuff/.elan
export PATH="$ELAN_HOME/bin:$PATH"
# CRITICAL on a shared/cgroup node: cap Lean's worker threads to the cores we
# actually own, else Lean spawns one thread per HOST core (32) inside a 16-core
# cgroup and thrashes (the earlier 4-core job stalled this way).
export LEAN_NUM_THREADS="${SLURM_CPUS_PER_TASK:-16}"
cd /gpfs/work5/0/gusr0688/fair_stuff/how-many-attention-heads-xor/head-complexity || exit 1

echo "=== host: $(hostname)  cpus: ${SLURM_CPUS_PER_TASK:-?}  LEAN_NUM_THREADS=$LEAN_NUM_THREADS ==="
date
echo "=== shared full validation ==="
if FORMALIZATION_DIR="$PWD" bash ../artifacts/scripts/validate.sh; then
  validation_rc=0
else
  validation_rc=$?
fi
date
echo "VALIDATION_RC=$validation_rc"
echo "DONE_SENTINEL"
exit "$validation_rc"
