# Large Head Complexity at Every Fixed Threshold Degree

## Statement

For every fixed integer $d\geq2$, there are Boolean functions on $n$ inputs with threshold degree exactly $d$ and

$$ H^{\ast}(f)=\Omega_d\left(\frac{n^{d-1}}{\log n}\right). $$

The counting argument uses the same Warren sign-pattern inequality as [theorem 26](../01_foundations_and_normal_form/026_counting_lower_bound.md).

Let $W_d(n)$ be the maximum head complexity among functions of threshold degree exactly $d$. Combining this lower bound with [theorem 198](../02_complexity_measure_upper_bounds/198_monomial_star_universal_head_bound.md) gives

$$ \Omega_d\left(\frac{n^{d-1}}{\log n}\right)\leq W_d(n)\leq\sum_{j=0}^{d-1}\binom{n-1}{j}=O_d(n^{d-1}). $$

> **Improvement.** The existing explicit quadratic separations show that two heads can be insufficient. This result makes the required head count grow almost linearly within the quadratic class, and almost as $n^{d-1}$ within every fixed degree class. It does not replace the theorem about any particular earlier witness function.

## Finite Statement

Put $N=dm$, $L=m^d$, and

$$ p=1+2H(N+1),\qquad R=\sum_{j=0}^{d-1}\binom Nj. $$

Assume $p\leq L$ and $0\lt R\leq L$. Define the two strict-pattern budgets

$$ B_H=\left(\frac{4e(H+1)L}{p}\right)^p,\qquad B_{\lt d}=\left(\frac{4eL}{R}\right)^R. $$

If

$$ B_H+B_{\lt d}\lt2^L, $$

then some function on $N$ inputs has threshold degree exactly $d$ and requires more than $H$ heads.

This finite implication is the kernel-checked theorem `exists_exact_fixed_degree_hard`. Its only analytic premise is `WarrenStrictSignPatternBound`. The dimension and budget inequalities are explicit hypotheses, not hidden archives or new axioms.

## Proof

### Theorem 1. A degree-bounded family shatters a large grid

Partition the inputs into $d$ blocks of $m$ bits. For every sign tensor $A\in\lbrace-1,1\rbrace^{[m]^d}$, define

$$ F_A(u^{(1)},\ldots,u^{(d)})=\mathbf1\left[\sum_{i_1,\ldots,i_d}A_{i_1\cdots i_d}\prod_{j=1}^{d}u^{(j)}_{i_j}-\frac12\gt0\right]. $$

This polynomial has degree at most $d$. On the product of the one-hot inputs, the sum is exactly the selected entry of $A$. Thus the family realizes all $2^L$ labelings of a grid of size $L=m^d$.

### Theorem 2. Count the low-head and lower-degree exceptions

Restrict the existing relaxed head-parameter polynomial family to these $L$ inputs. It has $p=1+2H(N+1)$ parameters and degree at most $H+1$ in those parameters. Warren's inequality bounds its strict sign patterns by $B_H$.

For lower degree, use one parameter for every squarefree monomial of degree strictly below $d$. There are $R$ such parameters. Evaluation on the selected grid is linear in these parameters, so Warren's inequality with polynomial degree one bounds these patterns by $B_{\lt d}$.

If the two budgets sum to less than $2^L$, some tensor labeling belongs to neither exceptional set. Its extension has degree at most $d$ by construction, and cannot have degree below $d$. It also cannot be computed with $H$ heads. This proves the finite statement.

`Results/RestrictedCounting.lean` proves this argument for any finite shattered input grid. `Results/FixedDegreeCounting.lean` constructs the one-hot tensor family and proves the exact-degree conclusion and the resulting bound on `degreeClassHeadMaximum`.

### Theorem 3. Asymptotic consequence

For fixed $d$, we have $R=O_d(m^{d-1})$. Choose $H$ to be a sufficiently small constant multiple of $m^{d-1}/\log m$. Then

$$ \log_2 B_H=O_d(Hm\log m),\qquad \log_2 B_{\lt d}=O_d(m^{d-1}\log m)=o(m^d). $$

The first exponent can be made at most $L/3$, and the second is at most $L/3$ for all sufficiently large $m$. Therefore their sum is less than $2^L$ and the finite theorem applies.

For an arbitrary sufficiently large ambient dimension, choose $m=\lfloor n/d\rfloor$ and adjoin the remaining dummy coordinates. Both head complexity and threshold degree are unchanged. Since $dm$ is within a constant factor of $n$, the stated lower bound follows. $\blacksquare$

The asymptotic estimates in this final step are proved here in prose. The Lean result exposes the exact finite budgets and does not yet formalize a big-O or big-Omega statement.

## An Explicit Unbounded Quadratic Family

There is also a weaker explicit family. Let $R=2^r$ and let $A_{ab}=(-1)^{a\cdot b}$ be the Walsh-Hadamard matrix. On $2R$ Boolean inputs, use the strict quadratic score

$$ \sum_{a,b}A_{ab}u_av_b-\frac12. $$

The one-hot restriction has sign matrix $A$. The classical spectral sign-rank bound gives sign-rank at least $\sqrt R$; see [Forster's paper](https://doi.org/10.1016/S0022-0000(02)00019-3). The existing sharper tangent bound from theorem 28 therefore gives

$$ 2^{H^{\ast}+1}-2\geq\sqrt R,\qquad H^{\ast}\geq\left\lceil\log_2(\sqrt R+2)\right\rceil-1. $$

For sufficiently large $r$, the function has threshold degree exactly two and unbounded head complexity. This application uses the already collected tangent-rank theorem, rather than importing the weaker rank inequality from the independent derivation. The spectral lower bound is not formalized in this repository.

## Subsumption Scope

The fixed-degree comparison in `HeadComplexity/AutomlrSubsumption.lean` keeps the exact degree-class maximum, nonemptiness of the class, Warren's estimate, and all finite budget conditions in both requirement bundles. Under that common scope, the new guarantee adds $H\lt W_d(N)$ to the old lower guarantee $d\leq W_d(N)$.

The certificate concerns this finite conditional contract. It does not certify the prose asymptotic estimates, eliminate Warren's premise, or subsume a theorem about a different named function.
