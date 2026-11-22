# Many Saddles in the Full Positive Denominator Domain

## Statement and scope

For integers $d\geq3$ and $k\geq1$, set $q=\lfloor(d+1)/2\rfloor$ and $n=d+k$. There is a fixed linear functional of the $2^n$ cube evaluations of one positive reciprocal head which has at least $q^k$ nondegenerate critical points in its full $n$-dimensional positive denominator domain. At each specified point its value is zero and its Hessian has exactly one negative eigenvalue.

This is an obstruction to a proposed small critical-point count, not a head-complexity lower bound. The head is positive at every cube vertex, so every parameter choice used below computes the same constant Boolean function. In particular, critical points must not be counted as distinct Boolean sign patterns.

## Rational profiles

Put $r_j=2+j/q$ for $0\leq j\lt q$, $e=d+1-2q\in\lbrace0,1\rbrace$, and

$$ P(r)=\prod_{j=0}^{q-1}(r-r_j),\qquad D(r)=\prod_{\ell=0}^{d}(r+\ell),\qquad R(r)=-1+\frac{P(r)^2r^e}{D(r)}. $$

The numerator of $R$ has degree at most $d$: the leading monic terms cancel. Thus partial fractions give

$$ R(r)=\sum_{\ell=0}^d\frac{a_\ell}{r+\ell},\qquad a_\ell=\frac{P(-\ell)^2(-\ell)^e}{\prod_{m\neq\ell}(m-\ell)}. $$

At every specified root,

$$ R(r_j)=-1,\qquad R'(r_j)=0,\qquad \alpha_j:=R''(r_j)=\frac{2P'(r_j)^2r_j^e}{D(r_j)}\gt0. $$

The roots lie in $[2,3)$. Moreover $|P'(r_j)|=j!(q-1-j)!/q^{q-1}\leq1$, so $\alpha_j\leq6/(d+2)!$. Consequently

$$ r_j(d+r_j)\alpha_j\lt\frac{18(d+3)}{(d+2)!}\lt2. $$

For the last inequality, the expression is $9/10$ at $d=3$, and its ratio at consecutive dimensions is $(d+4)/(d+3)^2\lt1$.

Use also the backbone profile

$$ R_0(r)=k\left(-\frac{5}{2r}+\frac{16}{r+1}-\frac{27}{2(r+2)}\right). $$

Direct differentiation gives $R_0(1)=k$, $R'_0(1)=0$, and $R''_0(1)=-2k$.

## The evaluation functional

Split the input into $x\in\lbrace0,1\rbrace^k$ and $y\in\lbrace0,1\rbrace^d$. The head and its denominator parameters are

$$ K_{x,y}(t,\beta)=\frac{1}{1+\sum_{i=1}^k t_i x_i+\sum_{a=1}^d\beta_a y_a},\qquad t_i\gt0,\quad\beta_a\gt0. $$

For $1\leq i\leq k$, define

$$ F_i(t_i,\beta)=\sum_{y\in\lbrace0,1\rbrace^d}\frac{a_{|y|}}{\binom d{|y|}}K_{e_i,y}(t,\beta). $$

Define $F_0(\beta)$ by using the evaluations $K_{0,y}$ with coefficient $a^0_{|y|}/\binom d{|y|}$, where $(a^0_0,a^0_1,a^0_2)=k(-5/2,16,-27/2)$ and all other $a^0_\ell$ are zero. Finally set $F=F_0+\sum_iF_i$. All coefficients of this functional are fixed and independent of the denominator parameters.

At $\beta=(1,\ldots,1)$, the values are $F_i=R(1+t_i)$ and $F_0=R_0(1)$. Choose each $1+t_i$ independently among the $q$ specified roots. This gives $q^k$ distinct points in the full positive orthant, at each of which $F=-k+k=0$.

## Gradient and Hessian

The symmetry of the address variables gives equal address derivatives in each summand. Homogeneity of $\sum_\ell a_\ell/(r+v\ell)=v^{-1}R(r/v)$ implies, at a root $r$,

$$ \partial_{t_i}F_i=0,\qquad \partial_{\beta_a}F_i=\frac1d,\qquad \partial_{\beta_a}F_0=-\frac{k}{d}. $$

Thus every coordinate of $\nabla F$ vanishes at each grid point.

Fix one such point and write $r_i=1+t_i$ and $\alpha_i=R''(r_i)$. The selector block of the Hessian is diagonal with entries $\alpha_i\gt0$. Differentiating the preceding homogeneity identity gives every selector-address entry:

$$ \partial_{t_i\beta_a}F=-\frac{r_i\alpha_i}{d}. $$

The address block has a common diagonal and a common off-diagonal entry. On the unit vector $(1,\ldots,1)/\sqrt d$ its eigenvalue is

$$ u=\frac{-2k+\sum_i r_i^2\alpha_i}{d}. $$

Indeed, the second derivative along the common address scale of a selector summand is $2R(r)+4rR'(r)+r^2R''(r)=-2+r^2\alpha$, whereas the backbone contributes $2R_0(1)+4R'_0(1)+R''_0(1)=0$.

On the orthogonal complement of that unit vector, the address eigenvalue is

$$ \tau=\frac{2k(d+1)-\sum_i r_i(d+r_i)\alpha_i}{d(d-1)}\gt0. $$

To verify this formula directly, the diagonal-minus-off-diagonal contribution of one selector summand is

$$ \frac{2}{d(d-1)}\sum_{\ell=0}^d\frac{a_\ell\ell(d-\ell)}{(r+\ell)^3}=\frac{2-r(d+r)\alpha}{d(d-1)}. $$

Expand $\ell(d-\ell)=-(r+\ell)^2+(d+2r)(r+\ell)-r(d+r)$ and substitute $R=-1$, $R'=0$, $R''=\alpha$. The same calculation with the backbone gives $2k/(d-1)$. Adding these expressions proves the claimed value of $\tau$. Its positivity follows from $r_i(d+r_i)\alpha_i\lt2$.

Only the uniform address direction couples to the selector block. Its Schur complement is

$$ u-\sum_i\frac{r_i^2\alpha_i}{d}=-\frac{2k}{d}\lt0. $$

Sylvester's law of inertia now proves that the Hessian has exactly one negative eigenvalue and no zero eigenvalues. In particular,

$$ \det(\nabla^2F)=\left(\prod_i\alpha_i\right)\tau^{d-1}\left(-\frac{2k}{d}\right)\neq0. $$

This proves all parts of the theorem. $\blacksquare$

## Consequences and exact limitations

For $k=d$, the number of specified critical points is $q^d$ on $n=2d$ input bits, with logarithm $(n/2)\log n+O(n)$. Thus no fixed bound of the form $C^n$ controls the number of nondegenerate critical points of arbitrary linear functionals of one positive head in the full denominator domain.

With $H$ independent heads and the same functional applied to their sum, the critical-point count is at least $q^{kH}$, and the Hessian has exactly $H$ negative eigenvalues. Quotienting parameter choices by head permutations leaves at least $q^{kH}/H!$ orbits. These are parameter orbits, not necessarily distinct evaluation tables. At $k=d$ and $H=\lfloor C2^n/n^2\rfloor$ for fixed $C\gt0$, their logarithm is of order $2^n\log n/n$, which is smaller than order $2^n$. This theorem therefore does not rule out a bound strong enough for the selected asymptotic target.

Nondegeneracy also implies, by the inverse function theorem applied to the gradient, that each of these finitely many critical points persists under sufficiently small perturbations of the functional coefficients. No assertion about distinct Boolean signs follows from that persistence.

## Independent finite audit

`verify_reciprocal_saddles.py` evaluates the functional, every gradient entry, and every Hessian entry using exact rational arithmetic for $d=5$, $k=4$, and $q=3$. It checks all 81 specified points, positive denominators, the displayed Hessian formula, and its negative Schur complement. The record is `reciprocal-saddle-verification.json`. It does not assert that the list exhausts all critical points. The general theorem above has not been formalized in Lean.
