# Storage Capacity and the Boolean Cube

## The square-root logarithm

The proposed exponent $3/2$ would follow from an appropriate bound on the order of $nH\sqrt{\log H}$ for the number of arbitrary Boolean labels that the exact architecture can memorize, uniformly when $H$ is exponential in $n$. Such a bound has not been proved here.

[Xiong, Kwon, and Oh](https://proceedings.neurips.cc/paper_files/paper/1997/file/56468d5607a5aaf1604ff5e15593b003-Paper.pdf) obtain a square-root logarithm in a replica calculation for sign committee machines. Their comparison with the rigorous Mitchison-Durbin bound does not make that calculation a proof for affine-ratio heads.

[Stojnic, Sections 1.1 and 3](https://arxiv.org/html/2312.08257v1), states rigorous upper bounds for treelike sign committee machines with fixed all-one output weights, zero thresholds, disjoint input blocks, and independent Gaussian input data. The input dimension tends to infinity with the number of hidden units fixed in the stated limit. These hypotheses do not cover unrestricted affine numerators and target-dependent positive denominators evaluated on the entire Boolean cube.

[Nishiyama and Ohzeki, Sections 2.1 and 2.2](https://arxiv.org/html/2404.13404v2), treat fully connected networks, but explicitly leave the analytic continuation and exchange of replica limits unjustified. Their weight vectors have a fixed Euclidean norm, and their displayed limit takes input dimension to infinity before width. Neither the heuristic calculation nor its order of limits proves a uniform bound in this run's regime.

## An exact sampling obstruction

Even a rigorous statement that random independently labeled samples are usually infeasible needs care when inputs are sampled with replacement from a finite cube. Such a statement can hold for the class of all Boolean functions because repeated inputs can receive conflicting labels.

Let $X$ be a set of size $N$, let $m$ inputs be sampled independently and uniformly from $X$, and give the samples independent fair binary labels. Let $K$ be the number of distinct sampled inputs. For the universal class of all Boolean functions on $X$, the exact fitting probability is

$$ P_{N,m}=\mathbb E\bigl[2^{K-m}\bigr]=\frac{m!}{(2N)^m}\mathrm{coeff}_{z^m}\bigl((2e^z-1)^N\bigr). $$

**Proof.** Conditional on the inputs, each of the $K$ occupied input locations admits two consistent label choices, among the $2^m$ possible sample-label vectors. This gives the expectation. For the coefficient formula, a given input location receiving $j\geq1$ samples contributes two label choices and exponential generating-function term $2z^j/j!$. An unoccupied location contributes one. Multiplication over all $N$ locations and assignment of the $m$ ordered sample positions gives the coefficient formula. $\blacksquare$

At $m=N$, this probability tends to zero exponentially despite the class being universal. Indeed, all coefficients of $(2e^z-1)^N$ are nonnegative, so evaluation at $z=1/2$ and the elementary Stirling bound $N!\leq e\sqrt N(N/e)^N$ give

$$ P_{N,N}\leq e\sqrt N\left(2e^{-1/2}-e^{-1}\right)^N,\qquad 0\lt2e^{-1/2}-e^{-1}\lt1. $$

The factorial estimate follows without an asymptotic remainder: concavity of $\log t$ on each interval between consecutive integers gives $\log(N!)-(\log N)/2\leq\int_1^N\log t dt=N\log N-N+1$.

The last strict inequality follows from $2u-u^2=1-(1-u)^2$ at $u=e^{-1/2}\in(0,1)$. Thus an infeasibility probability tending to one for independent labels and repeated cube samples does not, by itself, refute universality on the cube.

## A sufficient quantitative comparison

For $m\leq N$, a class universal on $X$ must fit every labeling whenever the sampled inputs are distinct. Consequently its fitting probability is at least

$$ \prod_{j=0}^{m-1}\left(1-\frac jN\right)\geq\exp\left(-\frac{m(m-1)}{2(N-m+1)}\right). $$

**Proof.** The product is the exact probability of distinct inputs. For $0\leq u\lt1$, integration of $1/(1-u)$ gives $-\log(1-u)\leq u/(1-u)$. Apply this inequality to each factor, replace every denominator $N-j$ by the smaller $N-m+1$, and sum $j$. $\blacksquare$

A fitting-probability upper bound strictly below this lower bound, for the exact attention architecture on uniform cube inputs, would refute universality at that head count. No such upper bound has been obtained. Establishing it with an unbounded improvement over the manuscript's count is a theorem-strength gap, not a consequence of the cited storage-capacity results.
