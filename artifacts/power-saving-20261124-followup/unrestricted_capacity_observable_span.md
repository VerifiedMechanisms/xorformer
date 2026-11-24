# Boolean inverse observations do not stably carry coordinate multiplication

## Statement and scope

This checkpoint rules out balancing a fixed commuting diagonal descriptor by using only its Boolean inverse observations. It does not rule out replacing the descriptor or repairing its truth table with a different representation.

For $0\leq\varepsilon\leq1/8$, take six positive denominator vectors with first slopes $(3+\varepsilon,2,1,1,3,2)$, second slopes $(2,1,3,2,1,3)$, constant coefficients $1$, and third slopes $1$. Every coefficient lies in $[1,4]$. Write $D_1(\varepsilon)$ for the diagonal matrix of first slopes, and let

$$ r_x(\varepsilon)_h=\frac{1}{1+w_{h1}(\varepsilon)x_1+w_{h2}x_2+x_3},\qquad \lambda=(1,1,1,-1,-1,-1). $$

All queries range over the entire three-dimensional Boolean cube. The following facts hold.

1. At $\varepsilon=0$, the functional $\lambda$ annihilates every $r_x(0)$, but $\lambda D_1(0)r_{(0,1,0)}(0)=-1/12$. Therefore the span of the Boolean inverse vectors is not invariant under coordinate multiplication.

2. For every $\varepsilon\gt0$, the eight Boolean inverse vectors span $\mathbb R^6$.

3. Throughout the cube, $|\lambda r_x(\varepsilon)|\leq\varepsilon$, whereas $|\lambda D_1(\varepsilon)r_{(0,1,0)}(\varepsilon)|\geq1/24$ when $\varepsilon\leq1/8$.

Thus a coordinate operator has norm at least $1/(24\varepsilon)$ in the norm whose unit ball is the absolutely convex hull of the Boolean inverse vectors, even though all poles stay in a fixed positive compact set and the observations have full rank.

## Exact calculation

Put $a_x=1+3x_1+2x_2+x_3\geq1$. The unperturbed six terms cancel for each query, and the perturbation changes only the first pole:

$$ \lambda r_x(\varepsilon)=\frac{1}{a_x+\varepsilon x_1}-\frac{1}{a_x}. $$

Its absolute value is at most $\varepsilon$. At the query $(0,1,0)$ the denominator of the first pole does not depend on the perturbation, so multiplication by its first slope gives

$$ \lambda D_1(\varepsilon)r_{(0,1,0)}(\varepsilon)=\frac{\varepsilon}{3}-\frac{1}{12}. $$

This has absolute value at least $1/24$ on the stated interval.

For full rank, use the six rows with binary indices $0,2,3,4,5,6$, in that order, and the displayed pole order. Their determinant is

$$ -\frac{\varepsilon(\varepsilon+2)(11\varepsilon+71)}{31104000(\varepsilon+4)(\varepsilon+5)(\varepsilon+6)}. $$

It is nonzero for every positive perturbation. The Lean proof avoids relying on an external determinant calculation: an explicit rational linear combination of the six annihilation equations first forces the first coefficient to vanish, and the remaining five coefficients then vanish by linear elimination.

## Consequence for changes of state basis

Let $K_\varepsilon=\mathrm{absconv}\lbrace r_x(\varepsilon):x\in\lbrace0,1\rbrace^3\rbrace$. For positive perturbations it has nonempty interior. Suppose an invertible state change $T$ gives a Euclidean comparison

$$ cB_2\subseteq TK_\varepsilon\subseteq CB_2,\qquad c,C\gt0. $$

The operator norm in the $K_\varepsilon$ gauge is at least $1/(24\varepsilon)$ by the displayed dual functional. The inclusions give

$$ \lVert TD_1(\varepsilon)T^{-1}\rVert_2\geq\frac{c}{24C\varepsilon}. $$

Consequently no state basis can simultaneously keep the Boolean observation hull uniformly round and keep the coordinate multiplication operators uniformly bounded. At zero perturbation, passing to the observable quotient does not even define these coordinate operators.

This is the first failing lemma in an observation-only balancing approach. Adding all coordinate products to the observable space would restore invariance, but changes the observations and reintroduces the ordinary-moment or inverse-system complexity that the approach sought to avoid.

## What this does not establish

The perturbed signed score is itself a difference of two reciprocal heads. Its six-head descriptor contains a removable exact ghost. The example therefore does not show that every comparable-width representation of any truth table is ill conditioned. It also does not contradict a data-dependent global compiler that removes projection ghosts before balancing.

## Formal verification

The file `formalization/HeadComplexity/Research/ObservableSpanInstability.lean` contains the kernel-checked declarations `score_zero`, `score_eq_difference`, `score_abs_le`, `multipliedScore_probe`, `multipliedScore_abs_ge`, `no_bound_at_zero`, `multipliedVector_not_mem_span`, `annihilator_eq_zero_of_pos`, and `arbitrarily_bad_full_rank_ratio`, together with the elementary positivity estimates used by them.

The matrix determinant formula and the convex-body operator-norm consequence above are written proofs. The Lean full-rank declaration proves the equivalent annihilator statement directly. No lower bound on unrestricted head complexity follows from this checkpoint alone.
