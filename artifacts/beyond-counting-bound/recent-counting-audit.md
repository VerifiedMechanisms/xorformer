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

A count of order $\exp(O(nH\log n))$ for the actual Boolean sign tables would be sufficient for the requested refutation. No such count has been proved. Separate affinity, positive interpolation uniqueness, a general coordinate-zero rank defect, and stability of denominator value-table generators have concrete counterexamples in this run. The surviving task is to control the distinct remaining signs, not merely to count parameter points or arbitrary linear-section components. Stating that task as a compression or identifiability lemma does not discharge it.
