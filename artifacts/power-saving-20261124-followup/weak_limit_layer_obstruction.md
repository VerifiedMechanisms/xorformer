# Many vanishing layers can reuse a cancelling head family

## Statement and scope

Counting successive nonzero layers of a weak limit does not by itself give a bound proportional to the number of heads and input coordinates. The construction below has uniformly positive denominators, allows only original admissible heads, and measures amplitude by the sum of the full-cube head norms. After that normalization the scores converge to zero and can have many distinct orders of vanishing at different inputs.

Every score in the construction has the same constant-positive truth table. Thus the example rules out charging an independent Boolean choice to every layer. It does not rule out a count that retains the shared factor structure, and it does not produce a universally low-margin truth table.

All statements in this note are written proofs. The four-bit example is checked by exact finite computation in [the verifier](verify_weak_limit_layers.py), not asserted as a kernel-checked theorem.

## A family with an exact product of leading factors

Fix $k\geq1$ and positive block sizes $r_0,\ldots,r_k$ with sum $n$. Define the mixed radices

$$ R_0=1,\qquad R_j=\prod_{i=0}^{j-1}(r_i+1). $$

In block $j$, indexed from zero, put

$$ P_{j,t}(x)=t^{R_jr_j}+\sum_{i=0}^{r_j-1}t^{R_ji}x_{j,i},\qquad 0\lt t\leq1. $$

These are strictly positive affine functions. Let $D(x)=1+|x|$, set $H=2^k$, and use one head for each subset $T\subseteq\lbrace1,\ldots,k\rbrace$:

$$ \phi_{T,t}(x)=\frac{(-1)^{|T|}P_{0,t}(x)}{D(x)+t\sum_{j\in T}P_{j,t}(x)},\qquad S_t(x)=\sum_T\phi_{T,t}(x). $$

Every denominator has strictly positive constant and slope coefficients. Its values lie between $1$ and $1+3n$ throughout the full cube for $0\lt t\leq1$. Arbitrary affine numerators over such denominators are admissible by the original-model construction `FracAtom.ofPositiveAffineRatio_eval`. There is no bias.

Repeated use of the fundamental theorem of calculus gives the exact mixed-difference identity

$$ S_t(x)=k! t^kP_{0,t}(x)\prod_{j=1}^{k}P_{j,t}(x)\int_{[0,1]^k}\frac{du}{\left(D(x)+t\sum_{j=1}^{k}u_jP_{j,t}(x)\right)^{k+1}}. $$

For one difference this is the identity $D^{-1}-(D+a)^{-1}=a\int_0^1(D+ua)^{-2}du$. Induction uses the next derivative of the reciprocal, whose sign cancels the alternating difference sign. Every factor in the displayed integral formula is positive. Hence $S_t(x)\gt0$ for every input and every positive $t$ in the stated interval.

In block $j$, let $m_j(x)$ be the first active coordinate index, or $r_j$ if the block is all zero. The distinct exponents within each affine factor give

$$ P_{j,t}(x)\sim t^{R_jm_j(x)}\quad\text{as }t\downarrow0. $$

The integral converges to $D(x)^{-(k+1)}$, since all its denominators converge uniformly to the positive number $D(x)$. Consequently

$$ S_t(x)\sim\frac{k!}{D(x)^{k+1}}t^{k+\sum_{j=0}^{k}R_jm_j(x)}. $$

Each tuple of block indices is attained on the Boolean cube. Mixed-radix uniqueness shows that the exponents are exactly the consecutive integers

$$ k,k+1,\ldots,k+L-1,\qquad L=\prod_{j=0}^{k}(r_j+1). $$

## Full-cube amplitude normalization preserves every layer

As $t\downarrow0$, the common numerator converges to $x_{0,0}$ and every denominator converges to $D(x)$. Since the cube is finite, convergence is uniform and the full-cube norms converge. The limiting norm of each head is $1/2$, attained at the singleton $x_{0,0}=1$ with all other bits zero. Thus

$$ M_t=\sum_T\|\phi_{T,t}\|_\infty\longrightarrow H/2\gt0. $$

Dividing all heads by $M_t$ preserves admissibility and makes the total amplitude exactly one. It preserves all $L$ orders of vanishing, changing only their positive leading coefficients. The normalized score converges to zero at every cube input. The individual limiting heads cancel exactly, while all their limiting denominators remain strictly positive.

With two heads, take $k=1$ and $r_0+r_1=n$. There are $(r_0+1)(r_1+1)$ distinct normalized layers, of order $n^2$ for balanced blocks. Therefore even a uniform linear bound in $nH$ on the number of layers is false.

More generally, for fixed $H=2^k$ and balanced blocks, the number of layers has order $n^{k+1}$. No fixed polynomial in $n$ added to a bound linear in $nH$ can control all these families as the fixed head count is varied.

## Failure at the logarithmic counting scale

The obstruction also applies when the comparison width is of the logarithmic fallback order. Let $m\to\infty$, take $n=2^m$, put $\ell=2m$, and set $k=n-1-\ell$. For all sufficiently large $m$, choose $\ell$ blocks of size two and all remaining blocks of size one. There are $k+1=n-\ell$ blocks and exactly $n$ bits. Then

$$ H=2^k=\frac{N}{2n^2},\qquad L=2H\left(\frac32\right)^{2m}. $$

Fix any positive constant $c$ and enlarge the allowed width to $K=\lfloor cN\log n/n^2\rfloor$. For sufficiently large $m$, $K\geq H$ and zero heads pad the construction without changing its amplitude. Since $K\leq2c(\log n)H$,

$$ \frac{L}{nK\log n}\geq\frac{(9/8)^m}{c(m\log2)^2}\longrightarrow\infty. $$

Thus a bound of order $nK\log n$ on the *number* of normalized weak-limit layers fails even at the explicit logarithmic fallback width. This is not an entropy lower bound: all these layers belong to one constant Boolean function. The construction does not establish the analogous layer-count failure at the larger aimed power-scale width.

## The first surviving counting lemma

A successful boundary count must encode the algebraic dependencies between layers. Here exponentially many subset-labelled heads have a mixed-difference identity, so all layers share only $k+1$ affine factors. The layer order is the sum of their mixed-radix orders; its multiplicity is not independent information.

The needed statement would bound the number of joint strict sign tables arising from such shared factorizations and their general analogues, allowing every denominator and numerator coefficient to depend on the target. Counting denominator face strata, normalized leading limits, or successive layer positions separately does not provide that bound.

## Exact four-bit instance

Take two blocks of size two. Then

$$ A_t=t^2+x_0+tx_1,\qquad B_t=t^6+x_2+t^3x_3,\qquad S_t=\frac{A_t}{D}-\frac{A_t}{D+tB_t}=\frac{tA_tB_t}{D(D+tB_t)}. $$

The sixteen Boolean inputs give all nine orders $1,\ldots,9$. The amplitude tends to one. The verifier computes the exact numerator coefficients and orders, checks the rational identity at several positive rational parameters, reconstructs each ratio with literal admissible original atom parameters, and checks the positive sign on the full cube.
