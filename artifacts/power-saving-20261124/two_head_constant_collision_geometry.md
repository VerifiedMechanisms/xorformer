# Constant collision limits of two heads

## Status

This is an auxiliary statement about normalized limiting quadratic tables. It does not bound the strict sign tables of arbitrary parameter paths, and it does not improve the unrestricted worst-case head lower bound. The distinction matters when the leading limiting table vanishes at some vertices.

## A sequential structural statement

Write an affine form in $n$ variables as a vector in $\mathbb R^{n+1}$, with its first coordinate the constant coefficient. Suppose two sequences of denominator vectors converge to the constant vector $e_0=(1,0,\ldots,0)$. Numerator vectors and biases may be arbitrary and unbounded. Clear the two denominators, absorb the bias into one numerator, and reduce by the Boolean relations $x_i^2=x_i$. This produces quadratic multilinear coefficient vectors $P_k$.

Assume the coefficient vectors are normalized to Euclidean norm one and converge to $P$. Then $P\neq 0$, and there is a set $I\subseteq\lbrace 1,\ldots,n\rbrace$ with $|I|\leq 4$ such that the quadratic part of the restriction of $P$ to $x_i=0$ for $i\in I$ admits a symmetric matrix completion of rank at most two. Here completion means that the off-diagonal entries are half the mixed quadratic coefficients, while the diagonal entries may be chosen freely.

Positivity and slope coherence are not used in this statement. It therefore applies, in particular, to admissible denominator sequences converging to a positive constant after normalization.

### Proof

Introduce a homogeneous coordinate $x_0$ for the constant term. Before Boolean reduction, every cleared numerator is a sum of two products of linear forms. Consequently it has a symmetric matrix $Q_k$ of rank at most four. Scaling the numerator to normalize its reduced coefficients scales $Q_k$ without changing this rank bound.

Use subscripts $0$, $i$, and $ij$ for the constant, linear, and mixed quadratic coefficients of $P_k$. Boolean reduction gives

$$ (Q_k)_{00}=(P_k)_0,\qquad 2(Q_k)_{0i}+(Q_k)_{ii}=(P_k)_i,\qquad 2(Q_k)_{ij}=(P_k)_{ij}\quad(i\neq j,\ i,j\geq 1). $$

Thus every spatial off-diagonal entry is bounded. After passing to a subsequence, each spatial diagonal entry either converges to a finite limit or has absolute value tending to infinity. Let $I$ contain the divergent indices, and write $J$ for its complement among the spatial coordinates.

If $I$ had at least five elements, the principal matrix on any five of them would be invertible for large $k$. Indeed, factor out its divergent diagonal matrix; the remaining matrix tends to the identity because all off-diagonal entries are bounded. This contradicts the rank bound. Hence $|I|\leq 4$.

Suppose first that $|I|\geq 2$. The spatial block $(Q_k)_{II}$ is eventually invertible, and its inverse tends to zero. Its off-diagonal blocks with $J$ are bounded. Taking the Schur complement inside the spatial principal matrix gives

$$ \mathrm{rank}\left((Q_k)_{JJ}-(Q_k)_{JI}(Q_k)_{II}^{-1}(Q_k)_{IJ}\right)\leq 4-|I|\leq 2. $$

The correction tends to zero. The block on $J$ converges because its diagonal and off-diagonal entries do. Rank at most two is closed under limits, so the limiting block provides the required completion.

Suppose next that $I=\lbrace i\rbrace$. Put $d_k=(Q_k)_{ii}$. The block on coordinates $0,i$ is

$$ T_k=\begin{pmatrix}(P_k)_0&((P_k)_i-d_k)/2\cr ((P_k)_i-d_k)/2&d_k\end{pmatrix}. $$

Its determinant divided by $d_k^2$ tends to $-1/4$, and every entry of its inverse tends to zero. Its cross-block entries with $J$ remain bounded by the displayed Boolean-reduction identities. The Schur complement after eliminating this invertible block has rank at most two and converges to the spatial block on $J$. Its limit again supplies the required completion.

Finally suppose $I$ is empty. Then the entire matrices $Q_k$ are bounded and converge after taking a subsequence. Let $W_k$ be the span of the two denominator vectors. If this span has dimension one along a subsequence, the limit matrix is a symmetrized product of the constant vector with an arbitrary vector, so its spatial block is zero. More explicitly, each $Q_k$ vanishes as a bilinear form on $W_k^\perp\times W_k^\perp$; the limiting hyperplane is $e_0^\perp$.

Otherwise pass to a subsequence for which the two-dimensional spaces $W_k$ converge in the Grassmannian to a two-dimensional space $W$. Because each denominator vector tends to $e_0$, the space $W$ contains $e_0$. Write $W=\mathrm{span}(e_0,d)$, replacing $d$ by a nonzero spatial vector. The limiting bilinear form vanishes on $W^\perp\times W^\perp$. Its spatial block therefore vanishes on $d^\perp\times d^\perp$. In an orthonormal basis starting with the direction of $d$, its matrix has the block form

$$ \begin{pmatrix}\alpha&\beta^\top\cr \beta&0\end{pmatrix}, $$

which has rank at most two. This proves the statement. $\blacksquare$

## Exact affine-product degeneracies

Let $M=m_0+\sum_i m_i x_i$ and $D=d_0+\sum_i d_i x_i$ be affine, with $D$ nonconstant. The product $MD$ is affine on the Boolean cube if and only if

$$ m_i d_j+m_j d_i=0\qquad(i\neq j). $$

If at least three slopes of $D$ are nonzero, these equations force every slope of $M$ to vanish. To see this, an index outside the support of $d$ has $m_i=0$ by pairing with any nonzero $d_j$. On the support, put $r_i=m_i/d_i$. The equations give $r_i+r_j=0$ for every distinct pair. Three indices imply all these ratios are zero.

If exactly two slopes of $D$ are nonzero, all slopes of $M$ outside those two coordinates vanish, and the two remaining ratios are negatives of one another. If exactly one slope of $D$ is nonzero, every slope of $M$ outside that coordinate vanishes, while its slope at that coordinate is unrestricted. These conditions are also sufficient by direct expansion.

## Why this does not prove a sign bound

A strict sign table represented along a degenerating path need only agree weakly with its first nonzero normalized limit. The limit may vanish at many cube vertices. Later terms can determine the strict labels at those vertices. The structural statement above controls one normalized limiting table, not the entire sequence of successive vanishing terms.

In particular, weak signs of low-rank matrices are insufficient by themselves: a matrix supported on one row can agree weakly with an arbitrary strict sign matrix, and has rank one. A successful use of this lemma would require an additional argument controlling all the successive zero sets and their later signs. No such argument is proved here.

## Verification status

The proofs above are written linear algebra arguments. They have not been formalized in Lean. No finite computation is used to establish the sequential structural statement.
