# Unimodular actual bases do not determine feasible labels

## Statement

There are two admissible original width-one scores in six variables with strictly positive denominator coefficients, the same seven affinely independent actual unit contacts including the origin, an integer-unimodular augmented contact matrix, and different full truth tables. Both scores have absolute value at least one on the whole Boolean cube.

This is kernel checked in `HeadComplexity.Research.UnimodularFeasibleBasisObstruction`, namespace `HeadComplexity.UnimodularFeasibleBasisObstruction.OriginBranches`.

## Exact counterexample

Coordinates are ordered from most to least significant bit. The contact vertex codes and their prescribed labels are

$$ J=(0,20,31,15,42,60,57), \qquad g=(1,-1,1,-1,-1,1,-1). $$

Write $z(x)=(1,x_1,\ldots,x_6)$. The two scores are $S_k(x)=A_k(x)/B_k(x)$, with coefficient vectors

$$ \begin{aligned} b_0&=(1,2,1,1,1,1,1), &a_0&=(1,-42,11,51,-15,-15,-27),\cr b_1&=(1,1,1,1,1,1,3), &a_1&=(1,-47,15,55,-19,-13,-31). \end{aligned} $$

Here $A_k=z\cdot a_k$ and $B_k=z\cdot b_k$. Every coefficient of either denominator is positive. The exact original-head constructor `FracAtom.ofPositiveAffineRatio` therefore applies, with arbitrary signed numerator coefficients retained.

The augmented row matrix $Z$ has rows $z(x)$ for $x\in J$. Its integer inverse is

$$ Z^{-1}=\begin{pmatrix}1&0&0&0&0&0&0\cr -2&2&-2&1&1&-1&1\cr 0&0&1&-1&0&0&0\cr 2&-3&2&-1&-1&2&-1\cr -1&1&-1&1&0&0&0\cr -1&1&0&0&1&-1&0\cr -1&1&-1&1&0&-1&1\end{pmatrix}. $$

`matrix_mul_inverse` verifies the product over the integers. `matrix_det_isUnit` concludes that $\det Z$ is a unit, which is the required unimodularity statement. Direct exact evaluation gives

$$ S_k(J_j)=g_j, \qquad |S_k(x)|\geq1 \quad\text{for every }x\in\lbrace0,1\rbrace^6. $$

The two full tables differ at vertex code $18$, namely $x=(0,1,0,0,1,0)$:

$$ S_0(x)=-1,\qquad S_1(x)=1. $$

The kernel declarations are `origin_contact`, `matrix_zero`, `matrix_succ`, `matrix_mul_inverse`, `matrix_det_isUnit`, `atom_eval`, `basis_values`, `full_cube_unit_slack`, `branch_disagreement`, and `original_computable`.

## What fails

A unimodular augmented Boolean basis makes the interpolant with constant denominator and unit labels integer valued and odd at every Boolean vertex. Its full-cube absolute gap is therefore at least one. That arithmetic observation does not show that its labels agree with every globally feasible branch. The counterexample above disproves the stronger claim that an origin contact, unimodularity, positivity, and the entire unit-gap system make the feasible chart have only one table.

The preceding `Origin` namespace separately checks an origin-containing unimodular chart where the constant-denominator interpolant has a different table from a genuine positive-denominator feasible score. The top-level namespace verifies that the earlier six-variable counterexample without an origin contact was already unimodular. These are supporting examples; the two strictly positive branches above settle the proposed uniqueness lemma directly.

No inference follows about relative margin, the number of tables in a general chart, or the worst-case head complexity. In particular, exponentially many feasible branches per chart have not been constructed. A density-sensitive upper bound for the number of branches is still compatible with this example.

## Search and verification

`search_origin_unimodular_branches.py` sampled arbitrary Boolean bases containing the origin, retained exact integer inverses, and tested positive integer denominator coefficients. It found the initial witness after $6408$ unimodular bases. A linear program suggested smaller coefficient vectors. The final vectors displayed above were then verified independently by exact arithmetic and the Lean kernel, so the theorem does not depend on the search, floating determinants, or linear-programming correctness.

The previous triangular-basis finite search covered a much narrower family. Its absence of counterexamples did not justify extrapolation to general origin-containing unimodular bases.
