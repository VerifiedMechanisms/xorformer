# Independent audit of the signed quadrature obstruction

## Verdict

I independently checked `signed_exponential_quadrature_obstruction.md`. The uniform separation theorem and the coherent two-head construction are correct. The proof permits signed coefficients, arbitrary real nodes, collisions, unbounded parameters, a free bias, and an arbitrary number of terms for the constant-denominator head.

This is a mathematical audit. It does not provide a new Lean theorem or an unrestricted product-atom lower bound. Retaining the original numerators and denominator directions is essential to the obstruction.

## Checks

**Chebyshev separation.** A nonzero sum of $M$ exponentials with distinct real exponents has at most $M-1$ real zeros counted with multiplicity, by repeated differentiation after dividing out one exponential. With $M=2K+1$, imposing double zeros at $K$ distinct nodes leaves a nonzero coefficient vector. The zero bound forces exactly those double zeros and no others, so the function has constant sign. Duplicate original nodes can be completed to $K$ distinct nodes without affecting annihilation of the proposed sum.

**Uniformity without parameter compactness.** The set of unit coefficient vectors defining nonnegative exponential sums on the entire real line is a closed subset of a finite-dimensional unit sphere. It is therefore compact. Every such nonzero function has a strictly positive integral on the positive half-line, and positivity of all query exponents makes that integral finite. The integral is the continuous linear form $\sum_i a_i/s_i$, whose minimum on this compact set is strictly positive. This proves a uniform positive Euclidean separation without any boundedness assumption on the proposed nodes or coefficients.

**Dual-rail evaluation.** The number of coordinate pairs is $J_0=2L+1$. Exactly one bit from every pair is active on a selected query. Their baseline contributions make $B=d$ and $r=1/d\pm\varepsilon$ exactly. The denominator constant is $3/4$ and all its slopes are positive. All slopes of $r$ are positive, including the smallest displayed slope $\gamma-\varepsilon=1$. Therefore the constant-denominator head with numerator $-r$ has the required coherent negative numerator slopes.

**From signs to approximation.** The opposite strict signs on the two queries with the same $B=d$ force the compiled constant-head coefficient $\alpha$ to be strictly positive. Dividing by it yields an approximation to $1/d$ with coordinate error strictly less than $\varepsilon$. The free bias counts as an additional exponential node. For $M=2^k$ divisor values and $K_0=M/2-2$, the choice of $M-1=2(K_0+1)+1$ queries exactly matches the uniform separation theorem. Hence every compiler needs at least $2^{k-1}-1$ nonconstant-head nodes.

**Dimension and strictness.** Bertrand's postulate gives distinct primes with $p_j\leq2^j$, hence $4L+2\leq2k(k+1)+6$. Taking $k=\lfloor\sqrt n/2\rfloor$ fits the construction in every $n\geq144$ and gives the stated lower bound $2^{\sqrt n/6}$. Extra coordinates receive positive coefficients and are zero on the selected queries. The strictifying free bias is chosen after padding, outside a finite exceptional set, so full-cube strictness is valid.

**Scope.** Changing the exponential directions permits the displayed four-term pure-product construction, and the separately verified two-head compilation theorem supplies three affine-times-product atoms. Thus this result excludes a target-dependent quadrature bridge with the displayed directions, while leaving a compiler with freely chosen directions open.
