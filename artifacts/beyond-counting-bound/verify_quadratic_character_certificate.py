"""Replay the finite quadratic-character obstruction using integer arithmetic."""
from pathlib import Path
import json
from math import isqrt


def main() -> None:
    path = Path(__file__).with_name("quadratic-character-certificate.json")
    data = json.loads(path.read_text())
    p = data["prime"]
    assert p > 2 and all(p % q for q in range(2, isqrt(p) + 1))
    seeds = data["seeds"]
    assert len(seeds) == 256
    for label, a in enumerate(seeds):
        assert a > 0
        for t in range(8):
            assert 0 < a + t < p
            expected = 1 if label >> t & 1 else p - 1
            assert pow(a + t, (p - 1) // 2, p) == expected
    for weight in range(4):
        assert pow(1 + weight, (p - 1) // 2, p) == 1
    print(json.dumps({"prime": p, "patterns": len(seeds),
                      "exact_character_checks": 2048,
                      "denominator_checks": 4, "status": "PASS"}))


if __name__ == "__main__":
    main()
