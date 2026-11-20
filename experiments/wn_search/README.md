# Searches for few-head representations (order of W(n))

Scripts used in the run "Worst-Case Head Complexity at Order 2^n/n^2". All searches are heuristic:
a success is certified exactly (rational arithmetic in `exact_verify`), a failure proves nothing.

| script | what it does |
|---|---|
| `search.py` | first attempt: Adam on a smooth margin loss over all parameters, then a max-margin LP in the numerators; weak (finds nothing below the Cover threshold). |
| `search2.py` | alternating max-margin LP in the numerators (denominators fixed) and Danskin subgradient ascent on the denominators (multiplicative updates, random restarts); also `alt_search_hinge` (hinge-loss variant, better when infeasible) and planted-instance generation. |
| `tropical.py` | simulated annealing in the tropical (dominance) sub-model: permutations, priorities and signs; counts non-monochromatic fibers. |
| `tropical_exact.py` | exact SAT decision procedure for the tropical sub-model (written by a subagent; see its header). |
| `pairs_search.py` | the same head family restricted to weight-two inputs (graphs on n vertices), a miniature where the linear and Warren predictions differ by a log factor. |
| `interp_count.py` | counts real solutions of the interpolation system S(x_j) = y_j at 2nH cube points (planted targets), i.e. the multiplicity that controls Warren tightness. |

Model: P-heads `(u.x)/(1+b.x)` with `b >= 0`; M-heads in complemented coordinates. Results are in `results/`
(logs and JSON with certified parameters). Summary of certified findings (20 Nov 2026):

- random 7-bit functions: 8 heads (none found with 7); random 8-bit functions: 11 to 14 heads (none with 10); random 9-bit functions: 22 and 24 heads, a random 10-bit function: at most 40 heads (bounded-range hinge search);
  fixed generic lists need nH >= N/2 (Cover), so these are genuinely nonlinear representations, but far from N/n^2;
- the optimizer does not recover the known n-head parity representations for n >= 6, so failures are uninformative;
- weight-two inputs: 16 vertices need 3 heads, 32 vertices 4 heads (linear threshold about 8);
- interpolation multiplicity at n = 5, H = 2: 19 distinct real solutions found (3 admissible) from 1500 starts.
