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
