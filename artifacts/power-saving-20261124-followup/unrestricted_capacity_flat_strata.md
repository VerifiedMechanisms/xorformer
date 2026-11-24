# Coordinate flat strata and the jet codimension obstruction

## Statement

Write $n=d+m$. Choose $H$ points in the positive orthant of the form

$$ c_h=(\lambda_{h1},\ldots,\lambda_{hd},u_1,\ldots,u_m),\qquad \lambda_{hi}\gt0,\quad u_j\gt0. $$

The free coordinates may be arbitrary. In particular, the points may all be distinct. Let $J$ be the full squarefree derivative matrix: its rows are squarefree monomials in the $n$ coordinates, and its columns are a point together with a coordinate derivative. Then

$$ \mathop{\rm rank}J\leq(m+1)2^d-1. $$

This bound does not grow with $H$. The parameter family is an open subset of a linear space of dimension $dH+m$; requiring distinct points removes only lower dimensional diagonals. Its codimension in the space of all ordered $H$ point configurations is $m(H-1)$.

The rank bound is kernel checked in `HeadComplexity.CoordinateFlatJetRank.derivativeMatrix_rank_le_sub_one`. The dimension calculation and the following consequence are written proofs.

## Exact factorization

Index a squarefree monomial by a pair $(P,Q)$, where $P\subseteq\lbrace1,\ldots,d\rbrace$ and $Q\subseteq\lbrace1,\ldots,m\rbrace$. Its derivative at $c_h$ in a free coordinate $i$ is

$$ {\bf1}_{i\in P}\left(\prod_{j\in P\setminus\lbrace i\rbrace}\lambda_{hj}\right)\left(\prod_{j\in Q}u_j\right). $$

Its derivative in a fixed coordinate $i$ is

$$ \left(\prod_{j\in P}\lambda_{hj}\right){\bf1}_{i\in Q}\prod_{j\in Q\setminus\lbrace i\rbrace}u_j. $$

For each $P$, these derivatives lie in the span of one column with dependence $\prod_{j\in Q}u_j$ and $m$ columns with dependence ${\bf1} _{i\in Q}\prod _{j\in Q\setminus\lbrace i\rbrace}u_j$. Thus $J$ factors through a space of dimension $(m+1)2^d$. The column for $P=\varnothing$ and the first type has zero coefficient in every derivative. Removing it gives the claimed bound.

`derivativeMatrix_factor` proves this exact matrix identity. `derivativeMatrix_rank_le_sub_one` uses the identically zero coefficient row to remove one dimension. Neither theorem requires positivity, so they apply in particular to the strictly positive configurations above.

## A universal linear slack does not repair the codimension charge

Fix any absolute constant $C$. Consider a proposed inequality that charges a rank defect to parameter codimension, allowing an additive $CH$ error:

$$ \mathop{\rm codim}\lbrace\mathop{\rm rank}J\leq r\rbrace\geq nH-r-CH. $$

Choose a fixed integer $d\gt C$ and put $r=(n-d+1)2^d-1$. The family above lies in the indicated rank locus and has codimension $nH-dH-(n-d)$. Consequently the proposed inequality would imply

$$ (d-C)H+(n-d)\leq(n-d+1)2^d-1. $$

This fails for sufficiently large $H$ compared with $n$. In particular, it fails at either target scale $H\asymp2^n/n^{3/2}$ or $H\asymp2^n\log n/n^2$ as $n$ grows. The counterexample uses strictly positive, distinct points and therefore survives restrictions excluding boundary points or coincident heads.

This generalizes the coordinate line example. A repair that simply adds any fixed multiple of $H$ to the failed codimension estimate still does not work.

## What this rules out

The example rules out a universal conversion of squarefree jet rank loss into an equal parameter codimension loss, even with an arbitrary fixed $O(H)$ allowance. It does not exhibit a badly conditioned truth table or a failure of a truth preserving margin repair.

These configurations instead admit cheap polynomial parameter charts. The separately proved `HeadComplexity.DenominatorCapacity.card_affineSlope_le` counts all truth tables represented by denominators in a varying affine space of dimension at most $d$, with arbitrary real linear numerator coefficients and arbitrary signed cancellation. Thus this particular bad jet stratum can be counted directly.

For unrestricted heads, the unresolved step is a complete classification or covering argument for all relevant denominator configurations, with a total chart cost small enough to improve the unrestricted count. Positive affine configurations with dependencies caused by Boolean relations must also be included; ordinary pole collisions and affine dimension alone do not describe every degeneration.
