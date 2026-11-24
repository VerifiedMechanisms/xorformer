# Separate affine fibers do not give a full contact basis

## The precise failed implication

The original score inequalities are affine in the numerator and denominator coefficients of any one head when all other heads are frozen. It is tempting to combine this fact with compactness and infer the existence of a feasible point having as many independent active constraints as there are total parameters.

That implication is false for general systems with the stated separate affinity. The example below is compact, has interior, has two affine parameter blocks, and can be translated strictly inside a positive coordinate box. Nevertheless its entire constraint Jacobian has rank at most three in a four-dimensional parameter space.

This is a counterexample to a proposed general lemma. It is not an original-head truth table, and it does not rule out an additional theorem exploiting the special Boolean evaluation rows of the original model.

## A compact explicit system

Write the parameter vector as $(a,b,c,d)\in\mathbb R^4$, with blocks $(a,b)$ and $(c,d)$. Impose

$$ |a-c|\leq1,\qquad |b-d|\leq1,\qquad ac+bd\leq1. $$

Each absolute-value inequality is two linear inequalities. The last inequality is affine in either block when the other is fixed. Every block fiber is therefore a convex polyhedron.

All five inequalities are strict at the origin. Their feasible set has nonempty interior. It is closed and bounded, because

$$ a^2+b^2+c^2+d^2=(a-c)^2+(b-d)^2+2(ac+bd)\leq4. $$

Thus it is compact. In particular every coordinate has absolute value at most two. Translation by $(3,3,3,3)$ places the whole set inside the open box $(0,6)^4$. Positivity restrictions and a compact surrounding box therefore do not supply missing active faces.

The five constraint normals are

$$ (-1,0,1,0),\quad (1,0,-1,0),\quad (0,-1,0,1),\quad (0,1,0,-1),\quad (-c,-d,-a,-b). $$

The second is the negative of the first and the fourth is the negative of the third. Hence the full normal matrix has rank at most three at every point. Every active submatrix has rank at most three as well. No point has four independent active constraints.

This failure does not come from an isolated singular point or a lower-dimensional feasible set. The rank bound holds everywhere, and the feasible set has interior.

## What this does and does not change

The already proved certificate in `PartialLinearCertificate.lean` remains valid: after fixing denominators, numerator and bias coefficients form a genuine linear program, and a bounded feasible polytope has a linear active basis. Its rational extension is formalized in `FeasibleRationalBasis.lean`.

The proposed replacement by a simultaneous basis in all numerator and denominator parameters needs a new selection theorem. Separate affinity in head blocks is insufficient. A norm-minimizing or lexicographically selected feasible point can require stationarity conditions in addition to the active unit-margin equations; counting those stationarity branches retains the unresolved algebraic complexity.

For the density-sensitive certificate route, one can instead keep the valid linear basis and seek a bound on its globally feasible extensions. With $L=nH+1$, the desired finite statement is that each actual Boolean basis chart has logarithmic extension count at most

$$ CnH\left(\log n+\log\frac{eN}{nH}\right). $$

The choice of $L$ basis rows and signs then has compatible entropy. Neither this chart estimate nor a suitable full-parameter replacement has been proved. Fixed-basis uniqueness is already false in the original model, including the recorded one-head six-variable example, so the missing statement must allow multiple feasible branches.

## Localization budget for the next attempt

Independent one-head choices do not automatically amplify to order $n^2H$ label entropy at critical width. On a specified set of only polynomially many Boolean queries, one head has only $O(n\log n)$ sign entropy, since its positive denominator can be cleared and its signs are affine thresholds. Obtaining order $n^2$ entropy from one head needs exponentially many relevant queries.

Disjoint address constructions spend approximately $\log_2 H$ input bits selecting a head. Near $H=N/\mathrm{poly}(n)$ this leaves only $O(\log n)$ independent address-local variables. A construction with overlapping supports would have to explain how it avoids this query budget while controlling contributions on every mixed Boolean vertex. Coherent denominator orientation also restricts direct concentration to all-zero or all-one anchored faces. These observations delimit the construction to investigate; they are not a proof of the desired global entropy bound.

## Kernel verification

`HeadComplexity/Research/BlockAffineNoVertex.lean` checks the strict feasible point, compactness, coordinate bounds, separate affinity in the two blocks, and the rank bound. Its main declarations are `HeadComplexity.BlockAffineNoVertex.feasible_isCompact`, `HeadComplexity.BlockAffineNoVertex.normals_rank_le_three`, `HeadComplexity.BlockAffineNoVertex.first_block_affine`, and `HeadComplexity.BlockAffineNoVertex.second_block_affine`.

The file introduces only this auxiliary example. It changes no definition or theorem of original head computability or worst-case head complexity.
