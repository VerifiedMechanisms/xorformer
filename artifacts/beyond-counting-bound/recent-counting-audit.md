# Recent Counting Results and the Remaining Gap

## Relative rank across sign orthants

[Basu and Parida, Theorem 5.6](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/bounds-on-the-realizations-of-zerononzero-patterns-and-sign-conditions-of-polynomials-restricted-to-varieties-and-applications/20F761E872FF702017C92778952FD46F), published in October 2026, bounds the maximum, over connected components of a semialgebraic set, of the minimum additive rank relative to an algebraic atom set. Its bound is

$$ \mathrm{mmrank}_{V,\Delta}(W)=\Omega\left(\frac{\log b_0(W)}{(p+1)(\log s+\log\delta+\log D+\log\log b_0(W))}\right), $$

where the atom set has dimension $p$ and degree $D$, and $W$ is described using $s$ polynomials of degree at most $\delta\geq2$. The theorem requires the real locus of each irreducible atom component to have the component's full dimension locally at every real point. This hypothesis has not been verified here for a chosen closure of the attention atoms.

The max-min definition does address signs, rather than exact real-table interpolation. Nevertheless, even an optimistic substitution cannot supply the desired improvement. For $N=2^n$ and $W=(\mathbb R\setminus\lbrace0\rbrace)^N$, one has $b_0(W)=2^N$ and may use $s=N$, $\delta=2$. With $p=\Theta(n)$ and the optimistic value $D=1$, the displayed expression is still only $\Theta(N/n^2)$. A larger degree worsens it. The complex zero-pattern theorem does not replace the real sign theorem.

## Analog formulas

[Turan and Vatan](https://homepages.math.uic.edu/~gyt/papers/Analog-JCSS.pdf) allow arbitrary real constants in bounded-fan-in analog circuits. Their general arithmetic-circuit Shannon scale is of order $2^{n/2}$. Their formula lower bounds use a Nechiporuk argument and include a polynomial lower bound for Element Distinctness. These are different complexity measures. Neither the general circuit count nor the displayed formula lower bounds imply a lower bound exceeding $2^n/n^2$ on the number of affine-ratio heads. No stronger transfer is asserted.

## Fractional set functions

[Han, Gomez, and Prokopyev](https://arxiv.org/html/2012.07235) study sums of the same algebraic type of ratios on Boolean inputs. They characterize when one ratio is submodular under stated coefficient and domain assumptions, and use this for optimization. Their standing numerator coefficients are nonnegative, and submodularity requires an additional condition; it is not a consequence of denominator positivity alone. The unrestricted signed-numerator classification problem here does not satisfy those hypotheses in general. Even imposing a relaxation to log-submodular denominator products already loses every tangent-sign restriction, as shown in [product-tangent-audit.md](product-tangent-audit.md).

## Status of the proposed compression

A count of order $\exp(O(nH\log n))$ for the actual Boolean sign tables in the critical regime $H=\Theta(2^n/n^2)$ would be sufficient for the requested refutation. A bound of this form for all $H$ is false already for $H=1$, because one head realizes every linear threshold function. No such count has been proved. Separate affinity, positive interpolation uniqueness, a general coordinate-zero rank defect, and stability of denominator value-table generators have concrete counterexamples in this run. The surviving task is to control the distinct remaining signs, not merely to count parameter points or arbitrary linear-section components. Stating that task as a compression or identifiability lemma does not discharge it.

## Oriented-matroid fewnomial bounds

[Bihan, Theorem A and Section 11](https://arxiv.org/html/2610.06435v3), revised November 12, 2026, counts nondegenerate positive roots using recursive bounds on chambers and flats of a Gale arrangement. The refinement subtracts roots forced in other chambers from a Bezout bound. Its application requires the relevant sign data, genericity or a justified perturbation, and a quantitative estimate for that recursion. Positivity of the original head denominators does not verify these conditions or provide the estimate.

There is also a concrete obstruction to applying a bound based only on a small excess of monomials. In the normalized cleared score at the all-one input, the bias term alone is

$$ \sigma\prod_{h=1}^H\left(1+\sum_{i=1}^n b_{hi}\right). $$

It contains exactly $(n+1)^H$ distinct monomials in the denominator variables. The remaining terms contain numerator variables and cannot cancel these monomials as a polynomial identity. Thus this direct expansion does not have a small monomial excess over its $2nH$ variables. A useful application of Bihan's stronger chamber-sensitive bound would require a new estimate exploiting the head system's special coefficient matrices; none is proved here.

## Uniform polynomial threshold counts

[Anthony, Theorem A](https://arxiv.org/html/2610.34378v1), posted October 25, 2026, proves logarithmic asymptotics for polynomial threshold counts uniformly over all degrees. With $m=\sum_{j=0}^d\binom nj$, the comparison is to the fixed-space arrangement count $Q_{n,d}=2\sum_{j=0}^{m-1}\binom{2^n-1}{j}$, with relative logarithmic error $O((\log n)^2/n)$.

This does not improve the head count. Clearing $H$ affine denominators and multilinearizing gives degree at most $\min(H,n)$. At the critical exponential value of $H$, this is $n$, where $Q_{n,n}=2^{2^n}$ and the bound permits every Boolean function. A universal improvement of this degree cutoff below $n$ for all $H\geq n$ is false: parity has threshold degree $n$ and is realizable with $n$ exact-model heads. Thus a head-specific counting invariant is still required. The fixed coefficient-space theorem does not supply a count for the union over target-dependent denominators.
