# Pure RoPE Search Certificates

These experiments explored alternative vanilla representations during the proof track starting at `bdca97f`. They are separate from the mathematical separation in [Theorem 22](../../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md). No optimization failure is used as a head-count lower bound.

## Exact successful fits

`search_many_head.py` generates genuine pure three-head models, searches for three vanilla affine fractions with uniformly oriented positive denominators, rationalizes successful fits, and checks every Boolean input with integer arithmetic. The free constant is absorbed into a numerator. The verifier checks both the pure labels and the vanilla labels, denominator positivity, and strict uniform slope signs.

| Input bits | Generation mode | Instances | Exact vanilla certificates |
| --- | --- | --- | --- |
| 8 | Quadratic cancellation probe | 30 | 30 |
| 10 | Quadratic cancellation probe | 100 | 100 |
| 10 | Reciprocal | 50 | 50 |
| 12 | Quadratic cancellation, wide weight range | 100 | 74 |
| 12 | Complemented oriented reciprocals | 50 | 50 |
| 12 | Three repeated reciprocal directions | 50 | 49 |

There are 353 verified certificates for 380 generated instances. The 74 certificates in the wide-range collection comprise 69 initial fits and five additional fits from endpoint-initialized retries. The retry sampled a snapshot of the original file while generation was still running. It did not retry every eventual failure. One repeated-direction sample had a floating fit but no verified rational certificate and is not counted as a success.

Raw generation records use `.jsonl`; independently checked integer witnesses use `.exact.jsonl`. The pure parameters and truth tables in those files are the authoritative inputs. Seeds are included in filenames; later records also record solver settings. The solver and rationalizer evolved during the run, so rerunning generation with the final script need not reproduce the same optimization trajectory. Certificate verification is independent of those choices.

Run the full integer verification from the repository root:

```bash
heavy python3 artifacts/rope/search/search_many_head.py --verify artifacts/rope/search/*.exact.jsonl
```

A typical new experiment is:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 heavy python3 artifacts/rope/search/search_many_head.py --n 12 --heads 3 --samples 100 --mode quadratic --spread 9 --restarts 16 --maxiter 3000 --seed 2026112424
```

The generator appends to its output files. Use a new seed or move existing output before rerunning this example.

## Exact obstruction for fixed endpoint denominators

`endpoint_dual_n12_sample9.json` contains a positive integer dual witness excluding the three endpoint denominator choices for sample 9 of the wide-range collection. It allows arbitrary affine numerators and a free constant with those fixed denominators. It does **not** exclude other three-head vanilla denominators.

For each signed label, multiply the cleared affine-numerator feature vector by its positive integer witness weight. The sum of every feature coordinate is exactly zero. A strict classifier in this feature span would make the sum of the signed scores strictly positive, a contradiction. Any classifier with zero scores only on negative labels can first be shifted downward by a sufficiently small free constant. The free constant already belongs to this feature span because one numerator may be a multiple of its denominator.

The witness has 38 supported vertices. `fixed_endpoint_dual.py --verify` checks the positive integer weights, all zero moment identities, the exact endpoint construction, and the source pure labels on all 4096 inputs. It uses only Python integer arithmetic in verification mode:

```bash
heavy python3 artifacts/rope/search/fixed_endpoint_dual.py artifacts/rope/search/endpoint_dual_n12_sample9.json --verify
```

This exact obstruction explains why fixing all denominators to the pure endpoint forms cannot be a universal conversion rule. It does not certify that sample 9 separates the head-count classes.

## A distinct numerical route

`search_variable_projection.py` eliminates affine numerators through a convex inner fit in an orthonormal feature basis and optimizes the denominator parameters outside it. Regularization acts on predicted scores, allowing large numerator cancellations. A 40-restart experiment on sample 9 remained unresolved. This is an optimization outcome, not a proof. The exact verifier is still required for every claimed successful fit.

The run used NumPy 2.4.6, SciPy 1.17.1, and SymPy 1.14.0. Certificate verification with `search_many_head.py` and `fixed_endpoint_dual.py` does not import these packages.
