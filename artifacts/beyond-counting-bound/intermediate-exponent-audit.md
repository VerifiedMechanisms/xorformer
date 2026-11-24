# Intermediate Exponents and Two Literature Transfers

## Strengthened candidate

The latest instruction prioritizes an exponent strictly between one and two, with a bound for every sufficiently large dimension. The target is the following, for some fixed $\alpha\in(1,2)$, $c\gt0$, and $n_0$:

$$ W(n)\geq c\frac{2^n}{n^\alpha}\qquad(n\geq n_0). $$

Multiplication by $n^2/2^n$ gives $n^2W(n)/2^n\geq c n^{2-\alpha}$, which is unbounded. Any fixed $\alpha\lt2$ suffices; the work does not require the particular exponent $3/2$ or the matching exponent one. A subsequence result would answer the original unboundedness question but would not complete the current eventual target. No such exponent improvement has been proved in this run. The manuscript's model is unchanged.

The [critical-scale address audit](critical-scale-address-audit.md) verifies that the factorial interpolation examples have logarithmic multiplicity of order $Hn\log n$ when $H$ is of order $2^n/n^\alpha$, including integer rounding. They do not refute the proposed full-cube entropy estimate in that range. The estimate for unrestricted adaptive denominators remains unproved.

## Exact scale of the counting gap

Put $N=2^n$ and $H=\lfloor cN/n^\alpha\rfloor$. For fixed $c\gt0$ and $1\lt\alpha\lt2$, the normalized manuscript estimate has logarithm at most

$$ 1+2nH\log_2\left(\frac{2e(N-1)}{n}\right)=(2c+o(1))N n^{2-\alpha}. $$

This exceeds the truth-table entropy $N$ by an unbounded factor. At $\alpha=3/2$ the factor is of order $\sqrt n$. Changing constants in that estimate cannot prove the candidate. The separately proved parameter-line obstruction also forbids replacing the degree $H$ by a head-independent degree in the original parameters. A different sign-counting mechanism would be necessary.

## Redkin's complexity measure

[Redkin's 1969 paper, pages 82 to 83 and 87 to 91](https://www.mathnet.ru/links/7b9fb0fdbcfea818fa2e0db60261840f/at10076.pdf) measures a threshold circuit by the sum of absolute integer input weights. Its lower estimate is asymptotically $2^{n-1}$ in that measure. A square-root factor occurs in a subsidiary counting error, not as a gate-count lower bound. Unrestricted real attention parameters have no imposed integer-weight budget. No transfer from this result to the requested head count has been proved.

## A recent sigmoid result

[Li, Reichman, Williams, and Wu, Theorems 1.4 and 6.5](https://arxiv.org/html/2611.21910v1) distinguish bounded-weight circuits with noticeable separation from unrestricted-weight circuits with zero separation. The former restriction theorem does not cover this problem's unrestricted margins. Their latter selection-function argument gives $n\leq2m\log_2(12m)$ by counting predicates of degree $m$ in $m$ programmable biases. That mechanism retains the logarithm at issue here. In addition, their logistic gates differ from the manuscript's affine-ratio heads. No theorem establishing an intermediate exponent follows from either statement.

The paper's arXiv identifier is `2611.21910`; an aggregator search result incorrectly associated its abstract with `2611.01055`, which is a different paper. The primary arXiv pages were checked directly.
