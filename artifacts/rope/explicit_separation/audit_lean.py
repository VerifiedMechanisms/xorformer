#!/usr/bin/env python3
"""Audit the axioms of every headline alias in Results/All.lean.

Build the repository first. This checks the complete scalar/original-vanilla
Boolean separation and all other headline declarations, including the literal
rotary matrix interpolation bridge and full residual architectural separation.
The lake/lean launcher acquires its own compute slot on the shared machine.
"""

from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[3]
FORMALIZATION = ROOT / "formalization"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    source = (FORMALIZATION / "HeadComplexity/Results/All.lean").read_text()
    aliases = re.findall(r"^alias ([A-Za-z0-9_]+)\s*:=", source, re.MULTILINE)
    assert aliases, "No headline aliases found"
    names = ["HeadComplexity." + name for name in aliases]
    proof = "import HeadComplexity.Results.All\n" + "\n".join(
        "#print axioms " + name for name in names
    ) + "\n"
    with tempfile.TemporaryDirectory(prefix="rope-axiom-audit-") as directory:
        path = Path(directory) / "Audit.lean"
        path.write_text(proof)
        result = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=FORMALIZATION,
            check=False,
            capture_output=True,
            text=True,
        )
        if result.returncode:
            raise RuntimeError(
                "Lean axiom audit failed; rebuild Results.All first.\n"
                + result.stdout + result.stderr
            )
    found = {}
    for name, axioms in re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout
    ):
        found[name] = {item.strip() for item in axioms.split(",") if item.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
        found[name] = set()
    assert set(found) == set(names), (
        "Unexpected Lean audit output", set(names) - set(found), result.stdout,
        result.stderr,
    )
    for name, axioms in found.items():
        assert axioms <= ALLOWED, (name, axioms - ALLOWED)
    print(f"Axiom audit passed for all {len(names)} Results.All headline aliases.")
    print("Only propext, Classical.choice, and Quot.sound occur.")
    print("Scope: literal rotary residual/original-vanilla separation and all headline results.")


if __name__ == "__main__":
    main()
