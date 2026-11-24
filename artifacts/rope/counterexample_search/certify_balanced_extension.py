"""Round proposed fits, then verify both architectures with exact arithmetic.

Unlike the fitting scripts, this checker uses only the Python standard library.
No unsuccessful rounding attempt has any lower-bound interpretation.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'higher_search'))
from verify_small import verify


def compile_record(record):
    fit = record['vanilla_search']
    if fit['status'] != 'floating_fit':
        return None
    n = record['n']
    truth = int(record['truth_table'], 16)
    for digits in [9, 12, 15, 18]:
        scale = 10 ** digits
        denominators = []
        numerators = []
        for b, a in zip(fit['B'], fit['numerators']):
            orientation = 1 if sum(b) > 0 else -1
            slopes = [orientation * max(1, round(abs(value) * scale))
                      for value in b]
            d0 = max(scale, sum(abs(value) for value in slopes) + 1)
            denominators.append([d0] + slopes)
            numerators.append([round(value * scale) * d0 for value in a])
        margin = None
        for mask in range(1 << n):
            z = [2 * ((mask >> i) & 1) - 1 for i in range(n)]
            d = [row[0] + sum(a * b for a, b in zip(row[1:], z))
                 for row in denominators]
            a = [row[0] + sum(b * c for b, c in zip(row[1:], z))
                 for row in numerators]
            value = (1 if truth >> mask & 1 else -1) * sum(
                a[h] * d[(h + 1) % 3] * d[(h + 2) % 3] for h in range(3))
            if value <= 0:
                break
            margin = value if margin is None else min(margin, value)
        else:
            result = {key: value for key, value in record.items()
                      if key not in ['vanilla_search', 'NRA']}
            result['vanilla_certificate'] = {
                'denominators': denominators, 'numerators': numerators,
                'minimum_integer_cleared_margin': margin}
            verify(result)
            return result
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('files', type=Path, nargs='+')
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    count = fits = exact = 0
    with args.out.open('w') as output:
        for path in args.files:
            for line in path.read_text().splitlines():
                record = json.loads(line)
                count += 1
                fits += record['vanilla_search']['status'] == 'floating_fit'
                result = compile_record(record)
                if result is not None:
                    output.write(json.dumps(result, separators=(',', ':')) + '\n')
                    exact += 1
    print({'records': count, 'floating_fits': fits, 'exact_certificates': exact})


if __name__ == '__main__':
    main()
