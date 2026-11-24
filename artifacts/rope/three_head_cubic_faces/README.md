# Cubic and quartic face searches

These scripts explore finite parity-face witnesses for the all-vanilla lower bounds in [Theorem 20](../../../theorems/03_rotary_attention/020_three_head_tripartite_face_obstruction.md) and [Theorem 21](../../../theorems/03_rotary_attention/021_four_head_quartic_face_obstruction.md). They did not certify a pure realization of either fixed pattern. The successful separation in [Theorem 22](../../../theorems/03_rotary_attention/022_explicit_pure_rope_separation.md) uses a different replication and sign-rigidity argument.

## Patterns and scope

The cubic pattern uses eleven coordinates in groups of sizes six, two, and three. Its 30 negative ordinary parity faces force the off-diagonal cubic coefficients of a six-by-six matrix to be negative. Six positive faces, each tying the six left coordinates to one bit, force positive column sums. The fixed backgrounds give 102 distinct inputs.

The quartic pattern uses fourteen coordinates in groups of sizes eight, two, two, and two. It similarly constrains an eight-by-eight coefficient matrix. Its fixed backgrounds give 281 distinct inputs. Both pattern generators check that overlapping prescribed labels agree.

Every numerical success would require exact pure parameters and strict verification of all required signs before using the lower-bound theorem. A coefficient matrix alone is insufficient. Numerical failures, fixed-denominator infeasibility, and infeasibility with bounded numerator coefficients have no unrestricted lower-bound meaning.

## Programs

All programs require NumPy and SciPy. The variable-projection programs also use the shared routines under [four_head_middle](../four_head_middle/). Run every search through `heavy` on the shared machine.

| Program | Purpose and options |
| --- | --- |
| `search_fixed_pattern.py` | Pure-three variable projection on the 102 inputs. The inherited options include `--out`, `--seed-file`, `--restarts`, `--iterations`, `--seed`, and `--regularizer`. Optional hard subsets are `--hard-parity`, `--hard-shared`, `--hard-anchors`, `--hard-columns`, and `--hard-both`. |
| `search_squared_margin.py` | Squared-hinge continuation of the same 102-point pattern, using the shared quadratic-program routines. |
| `search_adaptive.py` | Keeps the cubic orientation constraints hard, then alternates numerator optimization and choice of face backgrounds. Options include `--out`, `--seed-file`, `--attempts`, `--rounds`, `--iterations`, and `--seconds`. |
| `search_mixed_integer_faces.py` | Bounded mixed-integer selection of one background per desired face. Options include `--seed-file`, `--out`, `--backgrounds`, `--margin`, `--seconds`, `--restarts`, and `--score-basis`. Infeasibility applies only to the specified denominator directions, bounds, margins, and background list. |
| `search_auxiliary.py` | Gives each face its own auxiliary context while imposing the full pure mass cone. The default uses 36 one-hot controls, for 47 total bits. `--binary-contexts` uses six controls, for 17 total bits. `--hard-both` keeps one ordinary and one tied face hard. Other options are inherited from the fixed-denominator driver. |
| `search_four_quartic.py` | Pure-four variable projection on the 281 quartic-pattern inputs. Supports the inherited options, plus `--hard-parity` and `--hard-anchors`. |

For example:

```bash
heavy python3 artifacts/rope/three_head_cubic_faces/search_fixed_pattern.py \
  --out /tmp/cubic-proposals.jsonl --restarts 8 --iterations 200 --hard-parity
```

JSON output records are numerical proposals or solver diagnostics, never automatic proof certificates. In particular, `minimum_margin`, `loss`, and solver feasibility statuses must be checked independently with exact arithmetic before making a mathematical claim.

## What the searches established

Some numerical cubic proposals matched 101 of the 102 fixed labels. Separate runs could preserve the chosen ordinary parity face or the six tied-coordinate faces, but no complete exact witness was obtained. Adaptive scans of the tested actual score tables did not find a full alternative witness system. These results are inconclusive about untested parameters.

The exact coefficient relaxations are stored separately as `exact_tripartite_projection_margin.json` and `exact_quartic_projection_margin.json` in [counterexample_search](../counterexample_search/). Their smallest verified orientation margins exceed $5.53\cdot10^{-5}$ and $1.21\cdot10^{-5}$ respectively. Their pure token weights and query weights are strictly positive. They certify the feasibility of the top-degree coefficient conditions only.

Independent context optimization was also explored in [search_local_contexts.py](../counterexample_search/search_local_contexts.py). Those offsets are a relaxation until they satisfy the shared auxiliary-coordinate conditions. The exact bridge and its limitations are documented in [pure_context_bridge](../pure_context_bridge/README.md). None of these failed or incomplete fits is used in the final separation proof.
