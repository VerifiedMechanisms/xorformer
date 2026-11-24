# Search For A Pure Rotary Head-Count Separation

No strict Boolean head-count separation was found in this historical two-head campaign. All 830 sampled two-head pure rotary classifiers have exact two-head vanilla certificates.

> **Updated status, November 24, 2026:** [Theorem 16](../../../theorems/03_rotary_attention/016_pure_rope_two_head_equality.md) now proves universal equality at two heads. The separate construction in [Theorem 22](../../../theorems/03_rotary_attention/022_explicit_pure_rope_separation.md) achieves a strict separation with three pure heads and between four and five vanilla heads. See its [certificate package](../explicit_separation/README.md) for the completed proof. The samples below remain exact certificates of this earlier campaign.

| Campaign | Bits | Samples | Vanilla certificates |
| --- | --- | --- | --- |
| Independent random heads, seed 20261124 | 8 | 30 | 30 |
| Independent random heads, seed 817263 | 10 | 500 | 500 |
| Independent random heads, seed 121212 | 12 | 200 | 200 |
| Suppress constant and linear Fourier terms, seed 771177 | 10 | 100 | 100 |

The samples are not exhaustive and are not necessarily distinct Boolean functions. This is evidence about these samples only, not a proof of universal equality. Among the independent random samples, 125 have an explicit checkerboard face, so they are not one-head classifiers. Seven ten-bit samples initially failed three numerical restarts; each succeeded after at most four further restarts. No optimizer failure is treated as a lower bound.

## Exact Verification

Run from the repository root:

```bash
heavy python3 artifacts/rope/search/certify_two_head.py \
  artifacts/rope/search/exact_n8_n10.jsonl \
  artifacts/rope/search/exact_n12.jsonl \
  artifacts/rope/search/exact_cancellation_n10.jsonl
```

Verification uses Python integers throughout and needs only the standard library. For every record and every cube input, it checks:

- strictly positive pure attention weights and query weight;
- the exact sign of the pure score after clearing denominators;
- strictly positive vanilla denominators with uniformly signed, nonzero slopes;
- the exact sign of the vanilla score after clearing denominators;
- agreement with the stored truth table.

Each vanilla certificate stores two affine numerators and denominators in centered coordinates, with the constant first. The actual score is the sum of the two ratios. The affine-fraction normal-form theorem turns these certificates into two vanilla heads. The pure certificates use the scalar normal form of Theorem 14; its interpolation proof supplies fixed-standard-frequency rotary realizations.

These finite certificates are checked in Python, not individually imported into Lean. The reported minimum integer margins are for unnormalized cleared polynomials, so their magnitudes are not conditioning or robustness claims.

## Reproducing The Search

Search requires NumPy and SciPy. Example campaigns:

```bash
heavy python3 artifacts/rope/search/search_two_head.py --n 8 --samples 30 --restarts 10 --seed 20261124
heavy python3 artifacts/rope/search/search_two_head.py --n 10 --samples 500 --restarts 3 --seed 817263
heavy python3 artifacts/rope/search/search_two_head.py --n 12 --samples 200 --restarts 10 --seed 121212
heavy python3 artifacts/rope/search/search_cancellation.py --n 10 --samples 100 --restarts 10 --seed 771177
```

The search optimizes vanilla denominators, then solves a linear feasibility problem for their numerators. `certify_two_head.py --out FILE INPUT...` rationalizes a campaign's successful fits and checks the results exactly. Later input files override earlier records with the same input dimension and sample index; use this only to merge refinements of the same campaign. Floating search traces are ignored by Git. The committed exact certificates are independently verifiable without rerunning optimization.

The cancellation campaign selects a combination of pure-head features whose degree-one Fourier component is small relative to its total variance. It then rounds all parameters and evaluates the resulting truth table exactly before fitting vanilla. This biases the search toward nonlinear scores; it does not guarantee high head complexity.

## Retained Embeddings Example

`retained_f7.json` is a separate certificate for the seven-bit orientation function. Run `python3 artifacts/rope/search/verify_retained_f7.py` to verify its two-head retained-RoPE realization and the rational atom construction at all 128 inputs. It is not part of the 830 pure-head search records, and it is not a two-head pure-RoPE certificate. The corollary to Theorem 15 proves that its retained complexity is two while its pure and vanilla complexities are three, using the existing vanilla lower bound from the cited research run.
