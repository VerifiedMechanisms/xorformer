#!/usr/bin/env python3
"""Run the repository's faithful GitHub math audit without the gh CLI.

The repository token is kept only in process memory. This script performs no
repository write through the API and never logs the token or request headers.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    "check_md_math", ROOT / "artifacts/scripts/check_md_math.py"
)
checker = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = checker
spec.loader.exec_module(checker)


def main():
    token = subprocess.run(
        ["ar-github-token", "VerifiedMechanisms/xorformer"],
        capture_output=True, text=True, check=True,
    ).stdout.strip()
    records = []
    failed = False
    for name in sys.argv[1:]:
        path = Path(name)
        findings, spans = checker.lint_file(path)
        body = json.dumps({
            "text": path.read_text(), "mode": "gfm",
            "context": "VerifiedMechanisms/xorformer",
        }).encode()
        req = urllib.request.Request(
            "https://api.github.com/markdown", data=body,
            headers={"Authorization": "Bearer " + token,
                     "Accept": "application/vnd.github+json",
                     "Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=60) as response:
            rendered = response.read().decode()
        render_findings, notes, count = checker.render_audit(
            str(path), rendered, checker.MATH_PAYLOAD_GH
        )
        findings += render_findings
        if count != len(spans):
            findings.append(f"source/render count mismatch: {len(spans)} != {count}")
        failed |= bool(findings)
        records.append({"file": str(path), "source_spans": len(spans),
                        "rendered_spans": count, "findings": findings,
                        "notes": notes})
    print(json.dumps(records, indent=2, default=str))
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
