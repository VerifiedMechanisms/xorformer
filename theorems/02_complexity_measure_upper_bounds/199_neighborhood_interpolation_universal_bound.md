# Neighborhood Interpolation and the Three-Halves Universal Bound

## Statement

Keep the attention model unchanged. Let $W(n)=\max_f H^{\ast}(f)$, and let $I_n$ be the least number of fixed attention-positive affine denominators whose affine-numerator fractions span every real-valued function on the Boolean cube. A free constant is allowed.

For every $n\geq8$,

$$ H^{\ast}(f)\leq W(n)\leq I_n\lt\frac{3\cdot2^n}{2n}. $$

For every $n\geq1$, writing $\gamma_o(Q_n)$ for the minimum number of open cube neighborhoods covering all vertices,

$$ \left\lceil\frac{2^n-1}{n}\right\rceil\leq I_n\leq\gamma_o(Q_n)\leq2^{n-\lfloor\log_2n\rfloor}\lt\frac{2^{n+1}}n. $$

If $n\geq2$ is a power of two, then

$$ I_n=\frac{2^n}{n}. $$

> **Improvement.** The uniform coefficient improves from $11$ in [theorem 198](198_monomial_star_universal_head_bound.md) to strictly below $3/2$. The interpolation result is stronger than a separate existence proof for each Boolean classifier: one denominator family works for every numerical target. The dimension lower bound concerns $I_n$, not the head count of each individual function.

The joint integer budget keeps every previous endpoint and, when $n\geq8$, additionally takes the minimum with

$$ \left\lfloor\frac{3\cdot2^n-1}{2n}\right\rfloor. $$

Thus existing sharper bounds in particular small dimensions remain available.

## Proof

### Theorem 1. Localization on open neighborhoods

For a cube vertex $v$, put $L_v(x)=d_H(x,v)-1$. It is affine, and its zero set is the open neighborhood $\Gamma(v)$ of $v$.

For every covered vertex $x$, choose a center $v$ and coordinate $i$ with $x$ obtained by flipping coordinate $i$ of $v$. Let $N_x$ be the coordinate literal detecting disagreement with $v$ at $i$. On $\Gamma(v)$, this literal is one at $x$ and zero at all other neighbors. Consequently,

$$ \frac{\varepsilon N_x(y)}{L_v(y)+\varepsilon}\to\begin{cases}1&y=x,\cr0&y\neq x\end{cases}\qquad(\varepsilon\to0,\ \varepsilon\neq0). $$

The matrix with one such column for every vertex therefore tends to the identity. Resolve its removable singularities at zero. Continuity of the determinant gives a nonzero determinant at some nonzero parameter, with all denominator evaluations nonzero. Clearing the row denominators preserves nonsingularity.

This argument temporarily uses unrestricted affine denominator coefficients. The cleared determinant is a polynomial in those coefficients and is nonzero at the constructed witness. If it vanished at every strictly positive coefficient tuple, polynomial extensionality on the product of the infinite sets $(0,\infty)$ would make it the zero polynomial. Therefore some strictly positive coefficients give a nonsingular matrix too.

Those denominators are genuine attention denominators. Inverting the matrix interpolates any target, and collecting its numerator columns by head gives a `ClearedSpanCertificate`. Hence

$$ I_n\leq\gamma_o(Q_n). $$

The Lean modules are `Results/AffineZeroSetInterpolation.lean` and `Results/OpenNeighborhoodCover.lean`. They prove the limiting, positive-coefficient transfer, and actual-head compilation steps without an external nondefectivity assumption.

### Theorem 2. Syndrome covers

Let a surjective binary linear map have columns $A\subseteq\mathbb F_2^r$. If $T+A=\mathbb F_2^r$, the preimage of $T$ is an open-neighborhood cover. Indeed, a syndrome $s=t+a$ moves to $t$ after flipping a coordinate with column $a$.

All syndrome fibers have the same size. The number of centers is therefore

$$ |T|\cdot2^{n-r}. $$

Taking $r=\lfloor\log_2n\rfloor$ and listing every syndrome among the columns, including zero, gives the single-kernel bound $2^{n-r}$. The zero column ensures that a codeword itself has a distinct neighboring center.

Two smaller additive covers improve the rounding constant. Integers below encode binary vectors:

$$ A_{12}=\lbrace17,18,20,23,26,31,34,39,56,58,61,63\rbrace,\qquad T_7=\lbrace0,6,10,20,22,48,49\rbrace\subseteq\mathbb F_2^6. $$

$$ A_{13}=\lbrace0,3,4,14,20,52,66,89,95,96,110,115,126\rbrace,\qquad T_{12}=\lbrace0,1,13,40,69,78,83,97,104,112,120,125\rbrace\subseteq\mathbb F_2^7. $$

Exact finite checks prove both sumset equalities and give preimages of every standard basis vector, establishing surjectivity. Cartesian lifting replaces $A$ by $A\times\mathbb F_2^s$ and $T$ by $T\times\lbrace0\rbrace$. Appending columns extends the construction to every greater input length.

For $k=\lfloor\log_2n\rfloor\geq3$, the resulting cover budgets are

$$ \gamma_o(Q_n)\leq\begin{cases}2^{n-k}&2^k\leq n\lt12\cdot2^{k-3},\cr7\cdot2^{n-k-3}&12\cdot2^{k-3}\leq n\lt13\cdot2^{k-3},\cr12\cdot2^{n-k-4}&13\cdot2^{k-3}\leq n\lt2^{k+1}.\end{cases} $$

Relative to $2^n/n$, the three budgets are respectively strictly below $3/2$, $91/64$, and $3/2$. This proves the claimed universal bound.

The Lean modules `Results/SyndromeCover.lean`, `Results/SyndromeLift.lean`, and `Results/SyndromeCoverCertificates.lean` prove fiber counting, lifting, and the finite base certificates. `Results/UniversalNeighborhoodBound.lean` proves the interval arithmetic and the preserved joint budget.

### Theorem 3. Interpolation width and its exact power-of-two values

For fixed denominators, each affine numerator space has dimension $n+1$ and contains the same constant function. Thus $H$ such spaces have total dimension at most $1+nH$. Spanning the $2^n$-dimensional cube function space requires

$$ 2^n\leq1+nH. $$

This gives the lower bound on $I_n$. When $n\geq2$ is a power of two, the single-kernel cover has $2^n/n$ centers, and the dimension lower bound rounds to exactly the same number. Therefore $I_n=2^n/n$. Together with the general upper bound, $I_n=\Theta(2^n/n)$. $\blacksquare$

`Results/FixedDenominatorInterpolation.lean` defines the attained minimum, reuses the existing theorem-30 dimension obstruction, and proves its three-halves upper bound and exact power-of-two values.

## Certificates and Scope

`HeadComplexity/AutomlrSubsumption.lean` certifies strict subsumption of the full previous integer universal budget. Both contracts use the same actual-head realization premise. At dimension $16$, the old budget permits the abstract head value $8192$, while the new strict budget is at most $6143$.

This is a comparison of numerical guarantees. It does not assert that some sixteen-bit function has head complexity $8192$.

The supplemental [construction verifier](../../artifacts/calculations/verify_automlr_constructions.py) independently checks the base covers, Cartesian lifts, and the separate optimality calculation for six target syndromes in the six-bit base group. That finite optimality statement does not make $3/2$ an optimal universal head coefficient.
