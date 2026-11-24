# Sparse routing and exact localization

## Status

This checkpoint proves a finite capacity bound for prescribed sparse routings and an exact support obstruction for scores of original attention heads. Both statements are kernel checked. Neither asserts that arbitrary original representations admit sparse routing, and neither improves the unrestricted asymptotic lower bound.

The declarations are in `HeadComplexity/Research/RowSparseRationalCapacity.lean` and `HeadComplexity/Research/BooleanPolynomialSupport.lean`. The audit file and build log accompanying this note record their transitive axioms and successful build.

## Finite routing capacity

Let $I$ be a set of $m$ query rows, $J$ a head index set, and $K$ a set of $p$ real parameters. For a prescribed routing $R:I\to\mathcal P(J)$, consider

$$ S_\theta(x)=C_x(\theta)+\sum_{h\in R(x)}\frac{A_{h,x}(\theta)}{B_{h,x}(\theta)}. $$

Each numerator, denominator, and bias polynomial has total degree at most one in the parameters. The coefficients are arbitrary reals, all denominators used on a row are positive, and all signed cancellation is allowed. Assume $|R(x)|\leq k$ for every row and $1\leq p\leq m$.

Multiplication by the positive product of the routed denominators gives a polynomial of degree at most $k+1$ on each row. The kernel-checked Warren theorem therefore gives

$$ |\lbrace\mathrm{sign}S_\theta:\theta\text{ admissible}\rbrace|\leq\left(\frac{4e(k+1)m}{p}\right)^p. $$

This is `RowSparseRationalCapacity.card_represented_le`. For a finite codebook $T$ of possible routings, `card_routing_union_le` multiplies the right side by $|T|$. The routing codebook and its cardinality require independent justification.

For example, with $m=N=2^n$, $p\asymp nH$, and $k\leq n^a$ for a fixed $a$, this has logarithmic capacity $O(nH\log n)$ at $H\asymp N/n^2$. A routing codebook of size $\exp(O(nH\log n))$ retains this estimate. Such a model cannot encode every truth table at width $O(N/n^2)$, because $nH\log n=o(N)$.

The unrestricted model has every head present in every row. Taking $k=H$ restores the usual degree factor and the $n^2H$ exponent. No sparse-routing reduction is proved here.

## Boolean minimum support

For a polynomial $P\in\mathbb R[X_1,\ldots,X_n]$, write $s(P)$ for the number of Boolean points where $P$ is nonzero. If $\deg P\leq d$ and $s(P)\gt 0$, then

$$ 2^n\leq 2^d s(P). $$

This is `BooleanPolynomialSupport.two_pow_le_degree_mul_support`. When $d\leq n$, `supportSize_ge_two_pow_sub` states $s(P)\geq 2^{n-d}$.

**Proof.** Induct on the dimension. Write the two coordinate restrictions as $P_0$ and $P_1$, and let $D=P_1-P_0$. The polynomial $P_0$ has degree at most $d$ and $D$ has degree at most $d-1$: expand in the split variable, and every positive power contributes a coefficient of degree at most $d-1$.

If $D$ vanishes on the smaller cube, the two restrictions agree and support doubles. Otherwise the induction hypothesis gives $2^{n-1}\leq 2^{d-1}s(D)$, while $s(D)\leq s(P_0)+s(P_1)=s(P)$. Constant degree and zero dimension are handled directly. The proof does not assume that $P$ is multilinear and does not infer nonzero Boolean restriction merely from a nonzero formal polynomial.

## Original unrestricted scores

For any $H$ original admissible heads, any real readout vector, and any real bias, let

$$ S(x)=c+\sum_{h=1}^H\phi_h(x). $$

If $S$ is nonzero somewhere, positive denominator clearing gives a polynomial $P$ of degree at most $H$ with exactly the same support. Consequently

$$ 2^n\leq 2^H|\lbrace x:S(x)\neq 0\rbrace|. $$

The exact original-head declaration is `BooleanPolynomialSupport.original_score_support_bound`. The fractional-atom version is `atom_score_support_bound`; `one_head_support_bound` gives $2^n\leq 2|\mathrm{supp}S|$ for a genuine single head and bias. All denominator parameters, real coefficients, head dimensions, and signed cancellation remain unrestricted.

Thus exact localization to at most $M$ rows needs $H\geq\log_2(N/M)$. In particular, a nonzero constant-size group cannot be exactly confined to a polynomial-size block when $n$ grows. Every nonzero single head score is nonzero on at least half the cube, so literal low row sparsity of the original individual heads is unavailable.

This obstruction concerns exact support. It does not bound values outside a block, forbid approximate localization, or prove that many dense heads cannot cancel globally. At the exponentially large target width, the support bound for the entire score is vacuous. A successful improvement must control dense interactions, justify a smaller routing codebook with suitable approximate control, or find another unrestricted structural bound.

## Why independent programming does not immediately supply the conjectured upper bound

Against a fixed background score $R(x)$, one affine-ratio head changes signs according to

$$ \mathrm{sign}\left(R(x)+\frac{A(x)}{B(x)}\right)=\mathrm{sign}(R(x)B(x)+A(x)),\qquad B(x)\gt 0. $$

This is linear in the numerator and denominator coefficients. On a polynomial number of designated rows, one independently varied head therefore provides only $O(n\log n)$ bits of sign capacity, even if its coefficients have arbitrary precision. Achieving $\Theta(n^2)$ independent labels per head requires exponentially many relevant observations or collective nonlinear interactions. Disjoint address constructions spend approximately $\log H$ input bits identifying a head, leaving only $O(\log n)$ bits near $H=N/\mathrm{poly}(n)$.

The routing bound formalizes one limit on collective interactions: polynomially many contributors per row, together with a sufficiently small justified routing codebook, still has only $O(nH\log n)$ capacity. The localization theorem explains why an exact sparse-routing implementation by a constant number of original heads per small block cannot be presumed. These are obstructions to specific constructions and proof shortcuts, not an unrestricted capacity theorem.
