# Three-head cubic closure obstruction

## Scope

This note proves a closure obstruction for *raw homogeneous cubic polynomials* obtained by clearing three oriented affine fractions. It does not prove a Boolean head-count separation. In particular, reducing powers on a Boolean cube or averaging repeated coordinate groups can discard exactly the coefficients used by the obstruction.

The closure argument below is a mathematical proof, not a Lean declaration. Its exact polynomial special case is kernel-checked as `HeadComplexity.ThreeHeadCubicObstruction.no_three_denominator_identity` in `formalization/HeadComplexity/Polynomial/ThreeHeadCubicObstruction.lean`. The accompanying squarefree countercertificate is checked both by `HeadComplexity.ThreeHeadCrossGroupCertificate.squarefree_coefficients` and independently with exact rational arithmetic by `verify_squarefree.py`.

## A compact denominator theorem

Let $V$ be a finite-dimensional real vector space, let $v \in V$, and let $L_1,L_2,L_3 \in V^{\ast}$ be linearly independent forms satisfying $L_i(v)=0$. Suppose $D_{h,r},N_{h,r} \in V^{\ast}$ for $h \in \lbrace 1,2,3\rbrace$ and natural $r$, and define

$$ P_r=N_{1,r}D_{2,r}D_{3,r}+N_{2,r}D_{1,r}D_{3,r}+N_{3,r}D_{1,r}D_{2,r}. $$

Assume $D_{h,r}(v)=1$ and all the denominator forms lie in a fixed compact subset of $V^{\ast}$. Then $P_r$ cannot converge coefficientwise to $L_1L_2L_3$.

**Proof.** Pass to a subsequence on which all three denominator forms converge. Define the projection

$$ \pi_{h,r}(x)=x-D_{h,r}(x)v. $$

It has image in the kernel of $D_{h,r}$. Since every $L_i$ annihilates $v$, the coefficientwise limit of every $P_r\circ\pi_{h,r}$ is the same nonzero polynomial $L_1L_2L_3$. On the other hand, for distinct $h,j,k$,

$$ P_r\circ\pi_{h,r}=(N_{h,r}\circ\pi_{h,r})(D_{j,r}-D_{h,r})(D_{k,r}-D_{h,r}). $$

Write $E_{ij,r}=D_{j,r}-D_{i,r}$ for $i \lt j$. These three edge differences are nonzero for all sufficiently large $r$: a zero difference would make one of the displayed projected polynomials zero. Normalize them to have Euclidean coefficient norm one and pass to another subsequence, obtaining limits $e_{12},e_{13},e_{23}$.

We use the following elementary compactness fact. If unit linear forms $a_r,b_r$ converge to $a,b$, and $c_ra_rb_r$ converges to a nonzero cubic $Q$, then the linear forms $c_r$ are bounded. Otherwise a subsequence of $c_r/\lVert c_r\rVert$ would converge to a unit form $c$, and division by $\lVert c_r\rVert$ would give $cab=0$. This contradicts the fact that the real polynomial ring has no zero divisors. After taking a subsequence, $Q=cab$ for a nonzero linear form $c$.

Apply this fact at each of the three vertices to the preceding projected polynomial identity, absorbing the two edge norms into its numerator factor. Thus, at each vertex, its two incident limiting edge forms are linear factors of $L_1L_2L_3$. They must be proportional to two *distinct* members of $L_1,L_2,L_3$, since these three factors are independent and hence pairwise nonassociated. This follows either by unique factorization in the real polynomial ring or by primality of a nonzero linear form. Consequently $e_{12},e_{13},e_{23}$ are linearly independent.

But the exact identity $E_{13,r}=E_{12,r}+E_{23,r}$ contradicts this. Divide it by the largest of the three edge norms and pass to a further subsequence. The three nonnegative norm ratios have limits in $[0,1]$, at least one of which equals one. This produces a nontrivial linear relation among $e_{12},e_{13},e_{23}$. $\blacksquare$

This proof covers coincident denominator limits, arbitrarily different collision scales, and unbounded numerator coefficients. No boundedness assumption on the numerator forms is made.

## Kernel-checked exact special case

The Lean theorem `no_three_denominator_identity` states that the monomial $x_0x_1x_2$ has no three-denominator identity with denominators $t+B_h(x)$, where the $B_h$ are homogeneous linear forms in three variables. Its numerator functions may even be arbitrary polynomial-valued functions of $t$. The proof substitutes $t=-B_h$ at each of the three denominator hyperplanes. The pairwise differences would give three pairwise distinct linear factors of $x_0x_1x_2$, contradicting their triangle relation. This theorem concerns a polynomial identity, not equality on a Boolean cube.

The closure extension additionally uses the compactness argument above; it is not claimed to be Lean-formalized.

## Consequence for oriented cubic polynomials

Fix coordinates on $V=\mathbb{R}^n$ and a vector $v$ all of whose coordinates are strictly positive. Consider raw cubic polynomials of the form

$$ P=N_1D_2D_3+N_2D_1D_3+N_3D_1D_2, $$

where each $D_h$ has strictly positive coefficients and the $N_h$ are arbitrary linear forms. If $L_1,L_2,L_3$ are independent and $L_i(v)=0$, their product lies outside the closure of this class.

Indeed, rescale each denominator to satisfy $D_h(v)=1$, absorbing the corresponding positive scaling factors into the numerator forms. The normalized denominators lie in the compact simplex of nonnegative coefficient vectors satisfying this equality. The theorem applies. A uniformly negative denominator direction can first be multiplied by minus one, with its sign absorbed into the numerators.

A zero denominator direction does not enlarge the closure: it can be approximated by strictly positive directions, choosing the approximation small enough for each fixed numerator list. Thus the conclusion also applies to the cubic homogeneous parts of all three-head vanilla cleared polynomials, including degenerate or constant denominator cases. The output threshold term can be absorbed into one numerator before taking homogeneous parts.

For example, the raw cubic

$$ (x_1-x_0)(x_3-x_2)(x_5-x_4) $$

lies outside that closure, by taking $v=(1,1,1,1,1,1)$. This is a polynomial statement. It is not a lower bound for its Boolean sign function.

## Exact failure after squarefree projection

The preceding obstruction is lost if only cubic coefficients on three distinct coordinate groups are retained. Let $B$ and $U$ be the following matrices, with rows defining denominator and numerator linear forms:

$$ B=\begin{pmatrix}2&2&1&3&2&2\cr2&2&2&2&1&3\cr1&3&3&3&1&1\end{pmatrix},\qquad U=\begin{pmatrix}-20/3&-116/15&-4&-56/5&-20/3&-20/3\cr-76/21&-4/3&-4/3&-4/3&-44/21&0\cr45/7&203/15&40/3&68/5&36/7&0\end{pmatrix}. $$

Every entry of $B$ is strictly positive. The squarefree cubic part of

$$ \sum_{h=1}^3 (U_h\cdot x)\prod_{j\neq h}(B_j\cdot x) $$

is exactly $(x_1-x_0)(x_3-x_2)(x_5-x_4)$. The verifier checks all twenty coefficients with `fractions.Fraction`; the matrices are stored in `squarefree_certificate.json`. Terms containing a repeated variable are nonzero and cannot be omitted when applying the closure theorem.

## Remaining Boolean obstruction

For mixed conjunctions on large repeated coordinate groups, a prospective argument would need to show that *every* three-head vanilla representation produces, after a justified reduction and normalization, raw cubics converging to the product of three independent mixed linear forms. Symmetrizing a cleared polynomial does not preserve its three-denominator representation. Keeping only coefficients on distinct groups is insufficient by the exact certificate above. Unrestricted numerators can diverge as denominators collide, so an argument that assumes uniformly bounded atom parameters is also insufficient.

No such all-admissible reduction or explicit finite Boolean counterexample is claimed here.
