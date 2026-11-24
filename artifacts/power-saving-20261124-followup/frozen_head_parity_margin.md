# A frozen residual forces small margin under every one-head replacement

## Statement and status

The kernel-checked theorem `HeadComplexity.FrozenHeadParityMargin.relativeMargin_le_of_frozen_heads` is in `formalization/HeadComplexity/Research/FrozenHeadParityMargin.lean`. It applies to genuine original-model heads, arbitrary replacement denominators, arbitrary real numerator coefficients, and a free replacement bias. Norms are on the entire Boolean cube.

Let $f(x)=-(-1)^{x_1+x_2+x_3}$ be odd parity. Fix original heads with residual $R$, and suppose a distinguished original head $\phi$ satisfies

$$ f(x)(\phi(x)+R(x))\leq\varepsilon\qquad\text{for every }x\in\lbrace0,1\rbrace^3. $$

If the sum of the frozen heads' supremum norms is at least one, then every admissible replacement head $\psi$ and every bias $c$ that strictly represent $f$ satisfy

$$ \frac{\min_x f(x)(c+\psi(x)+R(x))}{|c|+\|\psi\|_\infty+\sum_{h\text{ frozen}}\|\phi_h\|_\infty}\leq\varepsilon. $$

This is a statement about **all replacements with this residual frozen**. It is not a statement about all representations of parity, which has well-conditioned alternative representations.

## Proof

Write the old and new heads as $A/B$ and $A'/B'$, with affine numerators and strictly positive affine denominators. This presentation includes both denominator orientations and constant denominators in the original model.

Parity annihilates every polynomial of degree at most two. Consequently,

$$ \sum_x f(x)B(x)B'(x)\left(c+\frac{A'(x)}{B'(x)}+R(x)\right)=\sum_x f(x)B(x)B'(x)\left(\frac{A(x)}{B(x)}+R(x)\right). $$

The difference is the parity sum of the quadratic polynomial $cBB'+A'B-AB'$. All weights $B(x)B'(x)$ are positive. Thus the minimum signed new score is at most the maximum signed old score. The new amplitude is at least the frozen amplitude, which is at least one. This proves the relative-margin bound.

The affine presentation, parity annihilation, weighted-average identity, absolute-gap inequality, and exact original-model relative-margin conclusion are all kernel checked. Seven declarations have only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

## An explicit arbitrarily ill-conditioned residual

The inherited construction in `artifacts/power-saving-20261124/frozen_head_boundary_obstruction.md` gives a concrete family. Put $s=x_1+x_2+x_3$ and

$$ A=s-\frac12,\qquad D=2s-3,\qquad B=1+x_1+2x_2+3x_3. $$

For $0\lt t\leq1/6$, define

$$ S_t=\frac{A}{B}+\frac{D-A}{B+tD}-\frac{D}{B+t(D-A)}=\frac{t^2 A D(D-A)}{B(B+tD)(B+t(D-A))}. $$

All three denominators have strictly positive coefficients and are strictly positive on the cube, so every head is original-admissible. At the four Hamming levels, the numerator $A D(D-A)$ has odd-parity sign and absolute value at most $15/4$. The denominator factors are at least $1$, $1/2$, and $1/2$. Hence

$$ 0\lt f(x)S_t(x)\leq15t^2. $$

Freeze the second and third heads. The third head has value $3/(1-5t/2)\geq3$ at the origin. For every replacement of the first head, including a new denominator and bias, the preceding argument therefore gives the stronger written bound

$$ \mathrm{relativeMargin}\leq5t^2. $$

The family identity, admissibility inequalities, and the constant $5$ are written proofs, not additional declarations in the new module. The kernel theorem applies immediately after supplying these hypotheses; its normalization with frozen norm at least one gives the slightly weaker bound $15t^2$.

## Block updates and the global gap

There is a direct written generalization. For parity on $n$ bits, replace $k$ heads while freezing all others. Multiply the score difference by the products of the old and new $k$ denominators. The resulting polynomial, including a free bias difference, has degree at most $2k$. If $2k\lt n$, parity annihilates it and the same positive-weight average proves that the new minimum signed score cannot exceed the old maximum signed score.

This rules out a general claim that a small block update must yield a definite absolute-gap improvement. It does not prevent a sequence of many updates, a simultaneous replacement of enough heads, or a new representation with extra heads. In particular, it does not count truth tables whose every comparable-width representation has tiny margin.

The natural one-head shared-chamber scaling also fails to lift directly to many heads. For $P=\sum_h A_h\prod_{j\neq h}B_j$ and $Q=\prod_hB_h$, scaling the two contact forms replaces $Q$ by a linear combination of $Q$ and $P$. This need not remain a product of affine forms. Already with two independent affine forms $B_1,B_2$ and $A_1=A_2=1$,

$$ Q+tP=B_1B_2+t(B_1+B_2)=(B_1+t)(B_2+t)-t^2 $$

is irreducible as a polynomial in the independent affine coordinates $B_1,B_2$ when $t\neq0$. For example, take $B_1=1+x+2y$ and $B_2=1+2x+y$. This is an obstruction to that exact continuous rational identity. It does not exclude a different factorization only on Boolean inputs or a sign-preserving new representation.

## Finite boundary-access searches

The companion `search_origin_boundary_access.py` explores fixed one-head unit-contact charts that include the origin. It minimizes the normalized intercept $b_0$ under the full-cube unit-gap inequalities and nonnegative denominator coefficients. Among 200,000 random dimension-six trials, 3,416 feasible chambers were found; among 100,000 dimension-eight trials, 382 were found. Every sampled chamber admitted a boundary solution with $b_0=0$. These are finite floating-point linear-program computations, not a proof of universal boundary access. The exact origin-contact counterexample in `origin_contact_counterexample.md` still refutes a constant-denominator repair preserving the full branch.

These searches do not resolve collective access for more than one head. The parity weighted-average identity identifies the first definite obstruction to simply extending one-head boundary moves while freezing the other heads.
