# Exact and approximate Hamming-layer gate costs

## Scope

These are value-localization obstructions for the original unrestricted xorformer heads. Every denominator may depend on the target; numerator coefficients and signed cancellation are arbitrary. The exact lower bound is kernel checked. The approximation lower bound and matching exact upper bound below are written proofs. None is a truth-table counting lower bound for the target width.

Write $|x|$ for the Hamming weight of $x\in\lbrace0,1\rbrace^n$. An original score has the form $S=b+\sum_{h=1}^H A_h/B_h$, with every $B_h$ positive on the entire cube and every head admissible in the original model.

## Exact positive gates require n heads

**Theorem.** Suppose $S\geq0$ on the cube, $S$ is nonzero somewhere, and every nonzero value lies on one Hamming layer. Then $H\geq n$. More generally, the conclusion holds if the nonzero values lie in one parity class.

**Proof.** Clear the positive denominator $Q=\prod_h B_h$. The polynomial $P=QS$ has degree at most $H$, including the bias term. If $H\lt n$, its alternating cube sum is zero:

$$ \sum_x(-1)^{|x|}P(x)=0. $$

Indeed, Boolean multilinearization preserves values and does not increase degree; each squarefree monomial of degree less than $n$ has zero alternating sum. On a single parity class all nonzero summands have the same sign, and at least one is nonzero. This is a contradiction.

The original-head theorem is `HeadComplexity.ExactLayerGateLowerBound.original_nonnegative_layer_gate_heads_ge` in `Research/ExactLayerGateLowerBound.lean`. The stronger parity-support version is `original_nonnegative_parity_support_heads_ge`; `original_weak_parity_heads_ge` allows arbitrary signs subject to weak parity agreement.

The bound is attained by an exact layer indicator using $n$ heads and a bias. Fix $k\in\lbrace0,\ldots,n\rbrace$, put $t=|x|$, and choose a scalar multiple of

$$ P(t)=\prod_{\substack{0\leq j\leq n\cr j\neq k}}(t-j),\qquad Q(t)=\prod_{h=1}^n(t+h) $$

so that $P(k)/Q(k)=1$. Then $P/Q$ is exactly the layer indicator on the cube. Partial fractions give a constant plus $n$ reciprocal terms with positive distinct poles. Their denominators have strictly positive coherent slopes, so these are genuine original heads. This upper bound is a written construction, not an additional kernel declaration.

## A constant-error central-layer gate needs square-root width

**Theorem.** There is an absolute $c\gt0$ such that, for all sufficiently large $n$, every original score satisfying

$$ \max_x\left|S(x)-\mathbf1_{\lbrace |x|=\lfloor n/2\rfloor\rbrace}\right|\leq\frac1{10} $$

has $H\geq c\sqrt n$.

This permits mixed denominator orientations, different directions for every head, arbitrary real numerators, bias, and signed cancellation. It requires uniform approximation of values. It does not claim a lower bound for sign representation of the central-layer function.

### Positive-literal expansion of the cleared denominator

An affine denominator positive on the entire cube can be written as

$$ B(x)=B_{\min}+\sum_i |b_i|\ell_i(x),\qquad B_{\min}\gt0,\qquad \ell_i\in\lbrace x_i,1-x_i\rbrace. $$

Thus the product $Q=\prod_h B_h$, after Boolean reduction, is a nonnegative linear combination of consistent literal monomials $x_A(1-x)_B$ with $A\cap B=\varnothing$ and $|A|+|B|\leq H$. Terms containing opposite literals vanish and repeated literals collapse. A strictly positive constant contribution remains.

Let $p(t)$ and $q(t)$ be the univariate symmetrizations of $P=QS$ and $Q$. Their degrees are at most $H$, and at integer $t$ their values are the respective averages on the Hamming layer. With falling factorial notation $(t)_a=t(t-1)\cdots(t-a+1)$, the preceding expansion gives

$$ q(t)=\sum_{a+b\leq H}c_{a,b}\frac{(t)_a(n-t)_b}{(n)_{a+b}},\qquad c_{a,b}\geq0,\qquad c_{0,0}\gt0. $$

Suppose $H\leq n/6$. On $t\in[n/3,2n/3]$, all factors in every summand are positive and every logarithmic derivative has absolute value at most $6H/n$. Taking the positive weighted average therefore gives

$$ \left|\frac{q'(t)}{q(t)}\right|\leq\frac{6H}{n}. $$

### A central window reduces to polynomial approximation

The case $H=0$ is impossible because a constant cannot approximate both a zero and a one to error $1/10$. If $H\gt n/200$, the desired lower bound already holds for large $n$. Assume $1\leq H\leq n/200$ and set

$$ k=\lfloor n/2\rfloor,\qquad L=\left\lfloor\frac{n}{100H}\right\rfloor\geq\frac{n}{200H}. $$

For sufficiently large $n$, the interval $[k-L,k+L]$ lies inside $[n/3,2n/3]$. The logarithmic derivative bound implies

$$ \frac{q(t)}{q(k)}\leq\exp(6HL/n)\leq\exp(0.06)\lt2 $$

throughout this interval. The pointwise approximation hypothesis gives

$$ |P(x)-\mathbf1_{\lbrace |x|=k\rbrace}Q(x)|\leq\frac1{10}Q(x). $$

Averaging this inequality on each layer is legitimate because $Q$ is positive and the target is constant on that layer. It follows that the polynomial

$$ R(y)=\frac{p(k-L+y)}{q(k)} $$

approximates the sequence $\mathbf1_{\lbrace y=L\rbrace}$ on the integers $0,\ldots,2L$ to error less than $1/3$. Off the central point the error is at most $1/5$, and at the central point it is at most $1/10$. This does not identify the average of $S$ with $p/q$; only the averaged inequality is used.

Paturi's symmetric approximate-degree lower bound implies that every polynomial giving this central spike to error $1/3$ has degree at least $c_0L$, for an absolute $c_0\gt0$. Apply it to the Boolean multilinearization of $R(\sum_{i=1}^{2L}y_i)$, whose degree does not exceed $\deg R$. Specifically, Theorem 4 has lower bound proportional to $\sqrt{m(m-\Gamma)}$; here $m=2L$ and $\Gamma=1$. [Paturi, STOC 1992, Theorem 4](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/Paturi_1992_stoc.pdf).

Consequently

$$ H\geq\deg R\geq c_0L\geq\frac{c_0n}{200H},\qquad H\geq\sqrt{c_0n/200}. $$

## Consequence for sparse-grid patching

The sparse-grid construction in `sparse_grid_compilation_and_outside_gap.md` controls a designated product grid but can have adverse values on deeper parts of the cube. Multiplying each module by an exact positive Hamming-layer gate cannot have constant cost: such a gate alone needs $n$ original heads. Even approximating the layer indicator uniformly to fixed small error costs at least order $\sqrt n$ heads. A product compiler could cost still more; the theorem does not assume that products of scores can be implemented by concatenation.

This does not rule out jointly refitting all patch modules, using signed corrections that are not nonnegative layer gates, or preserving only labels on most cube points. Those are separate access questions. In particular, a central layer has small uniform probability, so the zero score already approximates its indicator on most vertices; the constant-error theorem is deliberately uniform in the vertex.

## Verification

`lake build HeadComplexity.Research.ExactLayerGateLowerBound` completed successfully with 4036 jobs. All eight declarations in `AuditExactLayerGateLowerBound.lean` have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. The positive-literal symmetrization, central-window argument, and exact Paturi hypothesis match were independently audited by the finite-margin agent, including direct inspection of the primary PDF. The approximation theorem and the matching rational upper construction remain written mathematics; no approximation theorem is claimed kernel checked.
