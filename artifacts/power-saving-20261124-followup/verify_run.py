#!/usr/bin/env python3
"""Build and transitively audit every committed Lean module changed in this run."""

import argparse
import datetime
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
BASE = "aa0cceb140ba75149353f92943b1fba78e7e0ec5"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", default="final")
    parser.add_argument("--skip-default", action="store_true")
    args = parser.parse_args()
    out = Path(__file__).resolve().parent
    head = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    changed = subprocess.check_output(
        ["git", "diff", "--name-only", BASE, head, "--",
         "formalization/HeadComplexity"], cwd=ROOT, text=True
    ).splitlines()
    modules = sorted({
        path.removeprefix("formalization/").removesuffix(".lean").replace("/", ".")
        for path in changed if path.endswith(".lean")
    })
    if not modules:
        raise RuntimeError("No changed Lean modules found")
    (out / f"{args.prefix}-modules.txt").write_text("\n".join(modules) + "\n")
    metadata = {
        "base": BASE,
        "head": head,
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "module_count": len(modules),
        "checks": [],
    }
    commands = []
    if not args.skip_default:
        commands.append(("default-build", ["lake", "build"]))
    commands.extend([
        ("research-build", ["lake", "build", *modules]),
        ("transitive-axioms", ["lake", "env", "lean", "--run",
         "../artifacts/scripts/AxiomCheck.lean", *modules]),
        ("main-print-axioms", ["lake", "env", "lean",
         "AuditBootstrapWeightedCounting.lean"]),
    ])
    failed = False
    for name, command in commands:
        logfile = out / f"{args.prefix}-{name}.txt"
        started = datetime.datetime.now(datetime.timezone.utc)
        with logfile.open("w") as handle:
            result = subprocess.run(command, cwd=ROOT / "formalization",
                                    stdout=handle, stderr=subprocess.STDOUT)
        elapsed = (datetime.datetime.now(datetime.timezone.utc) - started).total_seconds()
        metadata["checks"].append({"name": name, "exit_code": result.returncode,
                                   "seconds": elapsed, "log": logfile.name})
        print(f"{name}: exit {result.returncode}, {elapsed:.1f}s", flush=True)
        failed |= result.returncode != 0
    metadata["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    metadata["all_passed"] = not failed
    (out / f"{args.prefix}-verification.json").write_text(
        json.dumps(metadata, indent=2) + "\n"
    )
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
