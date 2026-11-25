# Exploratory feasible-basis searches

These two searches were run earlier in this research period under `heavy`. They use floating-point linear programming and tolerance tests. Their outputs are exploratory evidence, not exact certificates or Lean proofs. Neither output establishes a universal branch-count or balancing theorem.

## General sampled bases

`search_feasible_basis_branches.py` samples threshold labels, finds a full unit-contact basis by linear programming, and samples denominator vectors in its positive simplex. With dimension eight and seed `239852`, the 300-second run processed 26,066 trials. The largest observed number of distinct feasible sign branches for one selected basis was four.

`feasible-basis-search-n8.json` preserves the four successive records and sample denominator vectors. The sampling does not enumerate all feasible branches. In particular, the maximum observed value four is not an upper bound on the branch count. Separate exact nonuniqueness and no-coordinate-ray results are proved in `UnimodularFeasibleBasisObstruction.lean` and `FeasibleConeNoCoordinateRay.lean`.

## Triangular unimodular bases

`search_triangular_balance.py` restricts the nonzero basis rows to an upper triangular Boolean matrix with diagonal one, adjoining the origin. It tests full-cube unit feasibility and then maximizes the normalized constant denominator coefficient. The dimension-twelve run with seed `774811` processed 5,200,637 trials; 1,268 passed its floating feasibility test. No recorded optimization result improved on the initial value one.

`triangular-balance-n12.json` records these totals. This special family does not cover general Boolean bases. Later exact examples show that a general feasible basis can exclude every coordinate ray. The new `UnitGapLeafDeletion.lean` also explains a limitation of sequential coordinate extensions: a coordinate whose containing contacts have only one label can be removed without violating any unit constraint.

The two search scripts remain available for reproducibility. A new heavy run should use `heavy python3 SCRIPT --n DIMENSION --seconds SECONDS --output OUTPUT.json`. Their finite numerical results are not dependencies of any theorem in this branch.
