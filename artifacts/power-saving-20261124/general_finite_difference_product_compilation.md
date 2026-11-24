# A finite-difference product compiler for arbitrary head count

## Statement and scope

Let $n\geq1$ and $H\geq1$. Suppose a strict Boolean sign table on $X=\lbrace0,1\rbrace^n$ is represented by

$$ S(x)=c+\sum_{h=1}^H\frac{A_h(x)}{B_h(x)},\qquad B_h(x)\gt0, $$

where every numerator and denominator is affine. There is a representation of the same strict signs by at most $2^H-1$ affine-times-positive-product atoms. This holds in particular for every original admissible representation. No denominator orientation or coefficient bound is needed beyond positivity on $X$.

Together with `product_atom_ball_upper_bound.md`, this gives the unconditional compiler bound

$$ K\leq\min\left\lbrace2^H-1,\frac{2^n}{2^{\lfloor\log_2(n+1)\rfloor}}\right\rbrace. $$

The first bound depends on the original head width; the second discards the representation and compiles its target table universally. Neither implies overhead sublinear in $n$ at the disputed exponentially large width scale.

## Exact expansion and limiting signs

Absorb the bias into the first numerator, replacing $A_1$ by $A'_1=A_1+cB_1$, and let $A'_h=A_h$ for $h\neq1$. Clearing positive denominators gives

$$ P(x)=\sum_{h=1}^H A'_h(x)\prod_{g\neq h}B_g(x),\qquad \mathrm{sgn}P(x)=\mathrm{sgn}S(x). $$

For $t\gt0$, define

$$ F_t(x)=\sum_{h=1}^H A'_h(x)\prod_{g\neq h}\bigl(e^{tB_g(x)}-1\bigr). $$

Since $(e^{tb}-1)/t\to b$ as $t\to0$, one has $t^{1-H}F_t(x)\to P(x)$ at every input. Every $P(x)$ is nonzero and $X$ is finite, so a single sufficiently small positive $t$ makes $F_t$ have the desired strict sign at every input. This includes $H=1$, when all displayed products are empty and $F_t=A'_1$.

Expanding each product and grouping equal subsets gives the exact identity

$$ F_t(x)=\sum_{T\subsetneq[H]}(-1)^{H-1-|T|}\left(\sum_{h\notin T}A'_h(x)\right)\exp\left(t\sum_{g\in T}B_g(x)\right). $$

There are $2^H-1$ proper subsets. Each coefficient is affine, and each exponential direction is affine. If the direction is $d_0+\sum_i d_ix_i$, then its exponential equals $e^{d_0}\prod_i(e^{d_i})^{x_i}$, a strictly positive product of one-bit factors. This proves the compiler bound. $\blacksquare$

For the original weak-negative convention, first decrease the free bias by a sufficiently small positive amount. The finitely many positive scores stay positive, and every nonpositive score becomes negative. This changes no target label and yields the strict representation needed above.

## The limitation of balanced clearing

This identity gives one atom for $H=1$ and three for $H=2$. The latter is sharp by the separately checked two-head adaptive separation. It is only an upper bound for larger $H$; the argument does not establish that exponentially many terms are necessary for their Boolean signs.

Grouping heads in a balanced binary tree does not reduce the displayed expansion automatically. If two partial scores have positive cleared denominators $Q_1,Q_2$ and numerators $P_1,P_2$, their sum has numerator $P_1Q_2+P_2Q_1$. Those products retain all the mixed denominator factors. A further sign-preserving reduction would need an additional argument exploiting the Boolean cube or cancellations jointly. No such reduction to $O(H\log n)$ or $O(Hn^\alpha)$ for fixed $\alpha\lt1$ is proved here.

## Verification boundary

The analytic sign bridge for an arbitrary finite family of positive denominators is Lean verified in `formalization/HeadComplexity/Research/FiniteDifferenceCompilation.lean`, by `HeadComplexity.FiniteDifferenceCompilation.uniform_finite_head_sign_compilation`. Its score is the sum of the affine-ratio terms after absorbing the bias, and its compiled expression is the sum of products of $(e^{tB_g}-1)/t$. The theorem supplies one positive interval on which the two strict signs agree at every point of an arbitrary finite input set. It assumes denominator positivity and a nonzero score at every input, without any coefficient, cancellation, or denominator-orientation assumption.

The independent build passed with only `propext`, `Classical.choice`, and `Quot.sound`. The subset expansion, its count $2^H-1$, the affine exponential factorization into Boolean product atoms, and the bias absorption in this general statement remain written mathematics. Thus the Lean theorem verifies the limiting sign argument, not a new unrestricted lower bound. The case $H=2$ has separate Lean verification in `TwoHeadProductCompilation.lean` and the direct original-model bridge `TwoHeadOriginalProductBridge.lean`. The universal product upper bound and the original worst-case head lower-bound question remain separate statements.
