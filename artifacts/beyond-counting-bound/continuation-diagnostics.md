# Continuation Stops Before the Unit Margin

## Scope

This file records a numerical diagnostic, not a theorem about infeasibility. The main lower-bound target remains unproved. Neither a failed solve nor a lost multiplier sign rules out other branches or representations.

## The branch being followed

The independently certified base example has sixteen input bits, three heads, and ninety-six selected vertices. Its score vanishes on those vertices, and its parameter Jacobian there is invertible. The exact signed norm dual determines labels $y_i\in\lbrace-1,1\rbrace$ and a local branch with

$$ S_{\theta(\varepsilon)}(x_i)=\varepsilon y_i,\qquad J(\theta(\varepsilon))\theta'(\varepsilon)=y. $$

The small-margin existence proof and full-cube audit are in `binary-active-minima.md`. They do not assert continuation to margin one.

`continue_active_minimum.py` follows this particular branch with seventy-digit arithmetic. It recomputes the unique signed multipliers from

$$ J(\theta)^{\top}\mathrm{diag}(y)\lambda=\nabla\lVert u\rVert^2. $$

At the base point, its numerical tangent agrees with the independently stored exact rational tangent to absolute error less than $8\cdot10^{-54}$. At nonzero margin, Newton residuals and multiplier values are numerical quantities. The other cube inequalities are checked in floating point. No interval enclosure of the continued branch is claimed.

## Observed endpoint

The run accepted twenty-three sample solutions. At

$$ \varepsilon=1.067279625984951701719123\cdot10^{-11}, $$

the least signed multiplier was approximately $3182.0563$, every denominator slope remained positive, and the floating-point minimum slack at an unselected vertex was approximately $1.42\cdot10^{-10}$.

At the next accepted sample,

$$ \varepsilon=1.3884635137804372122348599\cdot10^{-11}, $$

one signed multiplier was negative, approximately $-51426.9624$. The denominator slopes were still positive, and the unselected-vertex slack check still passed numerically. The program stopped at this loss of the necessary multiplier sign. It neither followed a changing active set nor certified the exact crossing location.

Thus this run does not extend the small-margin minimum to margin one. It also supplies no universal obstruction to doing so by a different route.

## Reproducible records

`experiments/active-minimum-continuation.jsonl` contains every accepted sample. `experiments/late-search-diagnostics.json` records its hash and the outcome of the independent binary-fiber search: 20,064 records, all unresolved, including two numerical failures. These records are deliberately marked as numerical diagnostics. They are not used as premises in any Lean theorem.

The separate full-cube norm searches include mixed denominator orientations and both fixed and variable origin constants. Their outcomes must be assessed separately. The exact one-head normalization repair in `origin-margin-repair.md` does not preserve a chosen local minimum or its multiplier signs.

## An independent stationarity replay rejects solver success

The first fixed-constant search used the squared numerator norm at the initial feasible point to scale its objective. Replaying trial 495 reproduces a solver-reported success with 38 nearly active constraints and 64 parameters. However, nonnegative least squares for the multiplier equation has relative residual approximately $0.0742$. Consequently this point does not pass even a numerical first-order audit.

`audit_unit_minimum_curvature.py` exposes this discrepancy. Three subsequent optimization passes, each rescaled by its current numerator norm, reduce the norm from approximately $245.43$ to $229.93$. The resulting point reaches the imposed parameter bound and violates a margin constraint by approximately $5.24\cdot10^{-6}$. It is not an interior feasible minimum either. The two complete floating-point replay records are retained in `experiments/unit-minimum-curvature-495.json` and `experiments/unit-minimum-curvature-495-refined.json`.

Those two records use the implementation at commit `7be65ed`, before the stable-denominator change below. Use that commit to reproduce their exact floating-point trajectories.

Both searches were restarted with these rescaling passes. Earlier records remain unresolved diagnostics, not local-minimum certificates. The optimization boxes, finite tolerances, and finite sample of starting points preclude any conclusion about all unrestricted real parameters.

## Stable denominators and an independent objective

For a negative-orientation head, write $p_i\gt0$, $C=1+\sum_i p_i$, and $b_i=-p_i/C$. The stable evaluation and derivative formulas are

$$ B(x)=\frac{1+\sum_i p_i(1-x_i)}{C},\qquad \frac{\partial B(x)}{\partial\log p_i}=\frac{p_i}{C^2}\left((1-x_i)\sum_jp_jx_j-x_i\left(1+\sum_jp_j(1-x_j)\right)\right). $$

These formulas avoid cancellation in the equivalent expression $1+b\cdot x$. They change no mathematical parameter domain. Finite-difference checks at a fixed mixed-orientation test point give a maximum score-Jacobian error below $1.6\cdot10^{-9}$ after this change. The new searches also use the wider log-parameter box with endpoints $-20$ and $20$. This is still a bounded numerical search.

`search_head_energy_minima.py` supplies an independent objective. For the normalized head contributions $r_h(x)$ and free constant $c$, it minimizes

$$ E(c,r)=c^2+2^{-n}\sum_x\sum_h r_h(x)^2 $$

subject to every signed cube margin being at least one. Its objective measures actual head-table values rather than numerator coefficients. The independent objective-gradient check has maximum error below $1.2\cdot10^{-9}$. A numerical linear-programming screen discards starting labelings reported to be linear thresholds; this screen is not a certified lower bound on any labeling. Candidate minima still require separate exact or interval verification.

A replay of head-energy trial 185 reproduced an interior feasible solver endpoint with seventeen nearly active constraints and forty-three parameters. Its relative nonnegative-multiplier residual was approximately $9.55\cdot10^{-6}$, and two fitted multipliers were zero. Numerical projected Hessians also had a negative eigenvalue near $-0.002405$ at three finite-difference scales. Because stationarity and the relevant ranks are not certified, this is not asserted to be a certified saddle or a minimum. The replay and curvature diagnostics are retained as `experiments/head-energy-replay-185.json` and `experiments/head-energy-curvature-185.json`.
