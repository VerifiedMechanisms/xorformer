# Three-Head Lower Bounds from Cubic Parity Faces

## Statement

Partition eleven Boolean coordinates into a block $X$ of size six, a block $Y$ of size two, and a block $Z$ of size three. Index the six pairs $(y_j,z_k)$ by $p=3j+k$.

Suppose a Boolean function has the following restrictions. Every face may have its own fixed background coordinates.

1. For every $i\neq p$, some three-dimensional coordinate face varying $x_i,y_j,z_k$ is negative three-bit parity.
2. For every pair $(j,k)$, some three-dimensional face varying $y_j,z_k$ and a single Boolean variable copied to all six $X$ coordinates is positive three-bit parity.

Here positive parity means that the product of the three signs is positive. Then every original vanilla xorformer computing this function requires at least four heads.

The hypotheses involve finitely many ordinary or tied-coordinate restrictions. They impose no global symmetry, no condition on unused input labels, and no restriction on the width or real parameters of the competing vanilla architecture.

## Proof

Clear the three positive denominators of any proposed vanilla score. The resulting polynomial is

$$ P=cD_0D_1D_2+N_0D_1D_2+N_1D_0D_2+N_2D_0D_1. $$

Its degree is at most three, and its sign is the classifier's sign. Let $C_{i,p}$ be the coefficient of $x_i y_j z_k$. The alternating sum on any three-dimensional face extracts this coefficient exactly, independently of the fixed background. Negative parity makes this sum strictly negative even when false inputs are permitted to have zero score. Hence every off-diagonal entry of $C$ is negative.

Tying all six $X$ coordinates to one variable makes the corresponding cubic coefficient equal to the column sum $\sum_iC_{i,p}$. Terms involving two or more $X$ coordinates cannot contribute to the coefficient involving both $y_j$ and $z_k$, because their total degree would exceed three. The positive parity restrictions therefore give strictly positive column sums.

Write the numerator slopes as $A_h$ and denominator slopes as $B_h$. For a head $h$, let $r,s$ be the other two heads and define

$$ W_{h,p}=B_r(y_j)B_s(z_k)+B_s(y_j)B_r(z_k). $$

Expanding the cubic coefficient gives a factorization

$$ C=A_XW^\top+V_XD^\top,\qquad (V_X)_{i,h}=B_h(x_i), $$

where the remaining matrix $D$ is unrestricted. Each column of $V_X$ has uniform sign or is zero. Each column of $W$ also has uniform sign or is zero, since its two summands have the same product sign. Independently changing the signs of these columns and their paired factors makes both distinguished factors positive or zero without changing $C$.

The positive-factor cross obstruction from [Theorem 19](019_four_head_local_orientation_obstruction.md) now applies with three columns and six rows. A square matrix with nonpositive off-diagonal entries and positive column sums is invertible and has the needed positive inverse action. Its factorization forces a zero bilinear expression between strictly positive factors. Zero columns are excluded by invertibility. This contradiction rules out every vanilla three-head model. Padding excludes smaller head counts. $\blacksquare$

## A fixed pattern with 102 inputs

A single consistent choice of backgrounds suffices:

- Use the all-zero background for every negative ordinary face.
- Use the all-one background outside the active coordinates for every positive tied-block face.

The overlapping prescriptions agree and cover exactly $102$ distinct eleven-bit inputs. The [exact verifier](../../artifacts/rope/tripartite_faces/verify_fixed_patterns.py) checks this count and consistency without a solver.

The pattern has a complete cubic polynomial realization. [cubic_completion.json](../../artifacts/rope/tripartite_faces/cubic_completion.json) lists an integer polynomial in sign coordinates, with every monomial of degree at most three. Its constant coefficient is one and every other coefficient is even, so it never vanishes on the cube. The verifier checks all $2048$ scores, all prescribed labels with minimum margin $23$, and the accompanying [truth table](../../artifacts/rope/tripartite_faces/cubic_completion_truth_table.txt). The truth table is ordered lexicographically in the eleven Boolean coordinates, with the final coordinate changing fastest.

This completion has threshold degree exactly three: the polynomial proves the upper bound, and any prescribed ordinary parity face proves the lower bound. The finite lower-bound theorem gives vanilla head complexity at least four. No pure three-head upper bound for this completion has been established.

## Formalization and architectural scope

- [ThreeHeadTripartiteCross.lean](../../formalization/HeadComplexity/Polynomial/ThreeHeadTripartiteCross.lean): `uniform_obstruction`, `pairFactor_uniform`, and `obstruction` prove the matrix argument, including independently oriented and zero factors.
- [ThreeHeadBooleanFace.lean](../../formalization/HeadComplexity/Polynomial/ThreeHeadBooleanFace.lean): `affine_blockFace`, `alternating_pos`, and `alternating_neg` prove the restriction and strict sign steps.
- [ThreeHeadCubicFace.lean](../../formalization/HeadComplexity/Polynomial/ThreeHeadCubicFace.lean): `cleared_eq`, `alternating_face`, and `centered_alternating_face` check the complete cubic identities.
- [ThreeHeadTripartitePattern.lean](../../formalization/HeadComplexity/Results/ThreeHeadTripartitePattern.lean): `Pattern` permits arbitrary backgrounds, `FixedPattern` specifies the $102$ inputs, and `not_computable_three` and `HStar_ge_four` state the original-model lower bound.

The last module invokes the repository's exact affine-fraction equivalence. Its conclusion therefore applies to all vanilla-admissible representations and to the original architecture with unrestricted finite width. The Lean declarations use no additional axioms or unfinished proofs. The particular integer cubic completion is independently checked by exact Python arithmetic; its complete polynomial and truth table are not incorporated into a Lean declaration here.

## Exact pure cubic coefficients

Three genuine pure atoms can realize a cubic coefficient matrix with all the required off-diagonal and column-sum signs. [exact_tripartite_projection.json](../../artifacts/rope/counterexample_search/exact_tripartite_projection.json) contains exact rational denominator and mass directions, token values, fixed-query parameters, and the coefficient matrix. [verify_tripartite_projection.py](../../artifacts/rope/counterexample_search/verify_tripartite_projection.py) checks every pure positivity constraint and all $36$ coefficient inequalities using rational arithmetic.

This certifies that the coefficient-level obstruction alone does not also exclude pure three heads. It does not show that the complete score meets the prescribed parity faces. Controlling the lower-degree score components, or finding different compatible face backgrounds, remains necessary before this route can establish a Boolean separation.

## Replacing singleton rows by regular coordinate blocks

The same lower bound permits a larger family of finite witnesses. Replace each singleton $x_i$ in the negative faces by a nonempty subset $I_i$ of the six $X$ coordinates, all moving together. Suppose the six subsets form a regular cover: each $X$ coordinate occurs in the same positive number $r$ of subsets. Keep the positive faces tying all six $X$ coordinates.

The new row coefficient is the sum over $I_i$ of the former row coefficients. Its distinguished denominator factor remains uniformly signed, because it is a nonempty sum of uniformly signed entries. The new column sum is $r$ times the original tied-block coefficient, so it remains positive. The same cross-matrix contradiction applies.

[ThreeHeadRegularBlockPattern.lean](../../formalization/HeadComplexity/Results/ThreeHeadRegularBlockPattern.lean) proves `not_computable_three` and `HStar_ge_four` for arbitrary such covers and arbitrary face backgrounds. Two verified choices are the six complements $I_i=X\setminus\lbrace i\rbrace$, each of size five, and the cyclic blocks $I_i=\lbrace i,i+1,i+3\rbrace$ with indices modulo six, each of size three. Their regularity declarations are `complementBlocks_regular` and `cyclicBlocks_regular`.

This extension adds certified lower-bound targets. It does not assert that any pure three-head function meets them.

## Auxiliary coordinates

The core eleven coordinates may be embedded into any larger cube. Each parity face may fix all auxiliary coordinates independently. The cubic alternating difference is independent of these fixed coordinates, because a polynomial of degree at most three has no term containing the three varying coordinates and an auxiliary coordinate.

The Lean declarations `ThreeHeadEmbeddedPattern.not_computable_three` and `ThreeHeadEmbeddedPattern.HStar_ge_four` prove the same lower bound for every input dimension at least eleven. This permits one separate auxiliary control coordinate for each of the thirty-six faces, without changing the obstruction or assuming that the model ignores those coordinates.
