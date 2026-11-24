# Two heads produce a sign-rank five star table

## Statement and scope

There are two admissible affine-ratio heads on a 37-dimensional Boolean cube whose values on a product of a five-point one-hot star and a 32-point one-hot star have sign rank five. This is a finite capacity construction and an obstruction to a particular low-rank replacement. It does not prove a lower bound for the original worst-case head complexity.

The certificate is in `two_head_star_rational.json`. The independent verifier `check_two_head_star_rational.py` uses only exact rational arithmetic. Z3 was used to discover the witnesses, but the verifier does not invoke it.

## Exact construction

For the five row indices use

$$ u=(9,15,11,1,3),\qquad z=(12,14,11,5,8),\qquad r=(18,28,30,-22,15),\qquad t=(23,27,-4,11,-30). $$

For each integer $j\in\lbrace 0,\ldots,31\rbrace$, the certificate gives a rational quadruple $(v_j,q_j,s_j,w_j)$ such that

$$ T_{ij}=\frac{r_i+s_j}{u_i+v_j}+\frac{t_i+w_j}{z_i+q_j} $$

has positive sign exactly when bit $i$ of $j$ is one. Every denominator is positive. For example, the column $j=26$, which has positive bits $1,3,4$ with zero-based indexing, uses

$$ (v_{26},q_{26},s_{26},w_{26})=(20,-9/2,-1045/2,429/4). $$

The exact verifier checks all 160 signs. To embed the whole table into the original coherent model, use five row coordinates and 32 column coordinates, and query the vertices having one selected row coordinate and one selected column coordinate equal to one.

Let $v_{\min}=\min_j v_j=-15/16$ and $q_{\min}=\min_j q_j=-9/2$. Put $\eta=1/64$. Define the first denominator to have constant coefficient $1/32$, row slopes $u_i-1+\eta$, and column slopes $v_j-v_{\min}+\eta$. Define the second denominator to have constant coefficient $15/32$, row slopes $z_i-5+\eta$, and column slopes $q_j-q_{\min}+\eta$.

Every constant and slope is strictly positive. At the selected vertex indexed by $(i,j)$, the denominators are exactly $u_i+v_j$ and $z_i+q_j$. Numerator slopes $r_i,s_j$ for the first head and $t_i,w_j$ for the second, with zero numerator constants, give exactly the displayed table. Such arbitrary affine numerators are permitted because both denominators are nonconstant.

## Sign rank

Any real matrix with these strict signs has row rank five. Otherwise choose a nonzero vector $a\in\mathbb R^5$ annihilating all its columns. Among the 32 prescribed columns is one whose coordinate signs agree with the signs of the nonzero coordinates of $a$. The dot product of $a$ with that column is strictly positive, a contradiction. The rank is at most five by the row dimension, so the sign rank is exactly five.

## A precise replacement obstruction

A quadratic table of the form

$$ L(x)+U(x)V(x), $$

with $L,U,V$ affine, has matrix rank at most four on any product of two one-hot stars. Indeed, writing row and column contributions separately expresses its restriction as a sum of four outer products: one row term, one column term, and the two mixed products from $UV$.

Consequently no score of this form has the same strict signs as the two-head table above on all the selected vertices. A nonzero scalar multiple or a positive scalar denominator common to the entire table does not change this conclusion.

This does not exclude constant-denominator collision paths with unbounded or moving numerators. Their first normalized limit may have zero entries, and later terms can determine the labels at those entries. Nor does it exclude a positive pointwise multiplier depending on both row and column: such a multiplier can change matrix rank. The sequential result in `two_head_constant_collision_geometry.md` is therefore not, by itself, enough to apply this strict sign-rank obstruction to every collision path.

## Verification status

The certificate is checked by exact finite rational arithmetic. The sign-rank argument and affine-product matrix-rank bound are elementary written proofs. No Lean verification is claimed.
