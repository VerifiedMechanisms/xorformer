# Weighted Diagonal Root Bound

## Kernel-checked statement

Let $w_i,e_i$ be positive integers. Suppose every monomial $x^a$ occurring in $p_i$ satisfies

$$ \sum_j w_j a_j \lt e_i w_i. $$

Then the system $x_i^{e_i}=p_i(x)$ has at most $\prod_i e_i$ distinct roots over any field. The corresponding nonzero diagonal perturbation bound is `HeadComplexity.PolynomialRootCount.weighted_perturbed_roots_card_le` in `formalization/HeadComplexity/Polynomial/WeightedDiagonalRootBound.lean`.

The proof does not invoke complex intersection theory. In the quotient by the equations, reduce a monomial divisible by $x_i^{e_i}$ using that equation. Every replacement has strictly smaller integer weighted degree. Strong induction shows that the quotient is spanned by monomials with $a_i\lt e_i$ for every $i$. Its dimension is at most $\prod_i e_i$. Distinct roots induce distinct algebra homomorphisms from this finite-dimensional quotient to the field, and the number of such homomorphisms is bounded by its dimension.

The module also proves quotient finiteness, the dimension bound, and finiteness and cardinality bounds for the root set. Five exported declarations were checked transitively with `#print axioms`; their only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The targeted build passed with 3162 jobs.

## Role in the research

This supplies the algebraic input for a weighted version of the existing real perturbation proof of Warren's theorem. For a polynomial of weighted degree at most $2D$, its derivative in coordinate $i$ has weighted degree at most $2D-w_i$. Taking $e_i=\lfloor 2D/w_i\rfloor$ gives a strict reduction bound and

$$ \prod_i e_i \leq \frac{(2D)^p}{\prod_i w_i}. $$

The analytic perturbation and sign-region arguments must still be connected explicitly. This root theorem by itself gives no improved unrestricted xorformer lower bound. In particular, it does not prove that arbitrary original head sums have a long-cluster representation.
