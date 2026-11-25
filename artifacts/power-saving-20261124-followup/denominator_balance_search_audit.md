# Denominator balancing probes and exact rejection of a numerical artifact

## Scope

These searches concern a single head with a fixed actual affine basis and fixed unit contact values. They do not optimize over all original representations of a truth table. All search outputs are floating exploration, except the separately reconstructed exact certificates described below. A failure to find an example is not an upper-bound theorem.

The scripts were run through `heavy`. The general basis search first solves a finite linear program for a separating numerator, selects an actual active basis, constructs its interpolation matrix, and searches the resulting fixed-label cone for the largest normalized denominator constant. Very small denominator coefficients make its floating feasibility test unreliable, so every claimed mathematical obstruction needs an independent exact reconstruction.

## Exact positive and negative checkpoints

`FeasibleConeNoCoordinateRay.lean`, commit `59eed8aa`, gives an exact ten-dimensional full-cube unit-basis branch whose closed denominator cone contains no coordinate ray. Its genuine strictly positive original witness and every coordinate-ray failure are kernel checked.

`UnitGapLeafDeletion.lean`, commit `b7b2811e`, proves that a coefficient can be decreased if all unit contacts on that coordinate's one-face have the same sign. Thus adjoining one new coordinate and one contact does not by itself amplify imbalance.

The rank-one search found the exact one-minority-contact example in `one_minority_balance_obstruction.md`: every denominator in that fixed branch has normalized constant at most $1/22$, and this supremum is attained in the closed cone. The integer witness, rational inverse matrix, dual certificate, and all cube inequalities are independently checked in `one-minority-balance-exact.json` and `check_one_minority_balance.py` and formalized in `OneMinorityBalanceObstruction.lean`.

The one-minority chart nevertheless has only one feasible full truth table, by `MinorityContactCapacity.one_minority_unique`. Small denominator constants do not imply large branch entropy.

## Exploratory runs

The archived runs have the following scope. The word “accepted” in their internal counters means only accepted by floating tolerances.

| Output | Trial count | Observation |
| --- | ---: | --- |
| `balance-vertex-cone-n9.json` | 71074 | No coordinate-ray counterexample; smallest recorded constant optimum was about 1/5. |
| `balance-deep-threshold-n12.json` | 10183 | Widely separated threshold weights gave no improving constant-balance record. |
| `balance-sparse-objective-n12.json` | 11428 | Smallest recorded optimum was about 1/7. |
| `balance-equal-scale-n12.json` | 11386 | Apparent zero optimum was rejected exactly below. |
| `balance-nonunimodular-n10.json` | 2898 | A nonunimodular basis was found; no asymptotic obstruction followed. |
| `balance-power-probe-n10.json` | 12 | Coordinatewise squaring of a denominator can leave its unit-gap cone; this is not an obstruction to another balancing deformation. |
| `rank-one-basis-balance-n10.json` | 28541 | Produced the independently certified 1/22 example. |
| `rank-one-basis-balance-n12.json` | 5314 | Tested 47664 candidate minority contacts in 3972 full-rank zero flats; no feasible candidate with a worse normalized constant was found. |

These finite computations do not establish a polynomial lower bound on the best normalized constant or an exponentially small counterexample.

## Exact rejection of the apparent zero optimum

The final record of `balance-equal-scale-n12.json` reported a strictly positive denominator and an optimum constant equal to zero. Reconstructing its interpolation matrix over the integers exposes a violated unit-gap constraint at vertex index $275$:

$$ -2b_0-2b_4\geq0. $$

This inequality rules out every strictly positive denominator in that fixed-label chart. On the reported floating witness its left side is approximately $-4.9913\cdot10^{-8}$, small enough to pass the original numerical tolerance. The exact matrix and witness are preserved in `balance-equal-scale-n12-rejection.json`. The matrix satisfies the prescribed basis equations exactly, so the rejection does not depend on rounding the interpolation equations.

This record is discarded as a mathematical counterexample. It does not show that a feasible original branch can force the constant coefficient to zero.

## First remaining inequality

The open fixed-basis question is whether every nonempty strictly positive full-cube unit branch contains a denominator satisfying $b_0/\sum_i b_i\geq n^{-C}$ for an absolute $C$. The exact 1/22 example disproves the strongest constant-denominator deformation, while none of these experiments resolves polynomial balancing.

Even a positive answer would still need a joint basis-selection and extension-count argument for many heads. Choosing an independent actual basis for each head already incurs order $n^2H$ entropy, and signed cancellation makes the other heads' residual target values arbitrary. The original unrestricted counting barrier therefore remains separate.

## Restricted triangular-basis branch probe

`search_triangular_chamber_branches.py` tested 42005 origin-containing upper-triangular Boolean bases in dimension ten, including deliberately enlarged inverse entries. For each prescribed contact-sign vector it sampled positive denominator vectors at several logarithmic scales and checked the complete cube unit-gap inequalities. The largest sampled number of full tables in any one chart was one. The data are in `triangular-chamber-branches-n10.json`. This is floating negative evidence from a restricted family, not a uniqueness theorem. General unimodular actual bases already admit two exact feasible branches, as recorded in `unrestricted_capacity_unimodular_basis.md`; the triangular experiment does not weaken those counterexamples.
