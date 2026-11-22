# Every Boolean Direction Occurs at One Hyperbolic Polynomial

## Statement and scope

For every $n\geq2$ there is an explicit homogeneous real polynomial $P_0$ of degree $n$ in $n+1$ variables with the following property. For every function $f:\lbrace0,1\rbrace^n\to[-1,1]$ there is a homogeneous polynomial $R_f$ of degree $n$ such that, for

$$ |\varepsilon|\leq\varepsilon_n:=\frac1{2(16n)^n},\qquad P_{f,\varepsilon}=P_0+\varepsilon R_f, $$

all of the following hold:

1. Every coefficient of $P_{f,\varepsilon}$ is strictly positive.

2. The polynomial is strictly hyperbolic with respect to $e=(1,\ldots,1)/(n+1)$: each polynomial $s\mapsto P_{f,\varepsilon}(z+se)$ has $n$ real roots, and they are distinct when $z$ is not a scalar multiple of $e$.

3. Its hyperbolicity cone contains the positive orthant, and the polynomial is real stable.

4. At every Boolean vertex $x$,

$$ \left.\frac{d}{d\varepsilon}\log P_{f,\varepsilon}(1,x)\right|_{\varepsilon=0}=\frac{f(x)}{P_0(1,x)}. $$

In particular, as $f$ ranges over sign-valued functions, these logarithmic variations give all $2^{2^n}$ Boolean sign tables at the same baseline polynomial of degree $n$.

The classical interior property for hyperbolic polynomials is due to Nuij. The proof here gives a particular baseline and a uniform perturbation radius for every Boolean direction. It uses an explicit root-bracketing argument rather than assuming openness. For the implication concerning the cone and real stability, the standard change-of-hyperbolicity-direction theorem is used as stated and proved in [Brändén, Proposition 1 and Theorem 3](https://math.berkeley.edu/~bernd/branden.pdf).

This is a counterexample to a proposed hyperbolic-polynomial relaxation, not an attention-head construction or a head lower bound. The path is not required to remain a product of positive linear factors.

## Construction

Write $d=n+1$, $m=\lfloor n/2\rfloor$, and $\eta=n-2m\in\lbrace0,1\rbrace$. For $z=(z_0,\ldots,z_n)$ define

$$ t=\sum_{i=0}^n z_i,\qquad y=z-te,\qquad r^2=\sum_{i=0}^n y_i^2=\sum_{i=0}^n z_i^2-\frac{t^2}{d},\qquad a_j=\frac jn. $$

Set

$$ P_0(z)=t^\eta\prod_{j=1}^m(t^2-a_j^2r^2). $$

Every $a_j$ is positive and at most $1/2$. The polynomial is homogeneous of degree $n$, and $P_0(e)=1$.

For a Boolean vector $b$, put

$$ L_b(z)=\prod_{i=1}^n\begin{cases}z_i,&b_i=1,\cr z_0-z_i,&b_i=0.\end{cases}\qquad R_f(z)=\sum_{b\in\lbrace0,1\rbrace^n}f(b)L_b(z). $$

Each summand is homogeneous of degree $n$. At $z=(1,x)$ with $x$ Boolean, $L_b(1,x)$ equals one if $b=x$ and zero otherwise. Consequently

$$ R_f(1,x)=f(x). $$

## Uniform bounds

### Lemma 1. Coefficient and evaluation estimates

The sum of absolute values of the coefficients of $R_f$ is at most $3^n$. Indeed, if $b$ has $k$ ones, expansion of $L_b$ has coefficient norm at most $2^{n-k}$. Summing over $b$ gives

$$ \lVert R_f\rVert_{\mathrm{coeff},1}\leq\sum_{k=0}^n\binom nk2^{n-k}=3^n. $$

Suppose $z=te+y$, $\sum_i y_i=0$, $\lVert y\rVert_2=1$, and $|t|\leq1$. Then $|z_i|\leq1+1/d\leq2$ and $|z_0-z_i|=|y_0-y_i|\leq2$. Every $L_b$ therefore has magnitude at most $2^n$, so

$$ |R_f(te+y)|\leq4^n. $$

These bounds are uniform in $f$ with $|f|\leq1$.

### Lemma 2. Strict positivity of every coefficient

Each quadratic factor can be written

$$ t^2-a_j^2r^2=\left(1+\frac{a_j^2}{d}\right)t^2-a_j^2\sum_{i=0}^n z_i^2. $$

Coefficientwise this is at least $(3/4)t^2$. Its diagonal coefficient is $1-a_j^2(1-1/d)\geq3/4$, and every off-diagonal coefficient is $2(1+a_j^2/d)\geq3/2$. All these coefficients are nonnegative, so multiplication preserves the coefficientwise inequalities. Therefore

$$ P_0\geq_{\mathrm{coeff}}(3/4)^m t^n. $$

Every monomial of total degree $n$ occurs in $t^n$ with a positive integer coefficient. Every coefficient of $P_0$ is thus at least $(3/4)^m$. Lemma 1 bounds the absolute value of each coefficient of $\varepsilon R_f$ by

$$ |\varepsilon|3^n\leq\frac12\left(\frac3{16n}\right)^n\leq\frac12(3/4)^n\leq\frac12(3/4)^m. $$

Every coefficient of $P_{f,\varepsilon}$ is consequently at least $(3/4)^m/2\gt0$. In particular the polynomial is positive on every nonzero point of the closed positive orthant, including $e$.

## Explicit real-rootedness proof

Fix $y$ with $\sum_i y_i=0$ and $\lVert y\rVert_2=1$. On this line the baseline polynomial is independent of $y$:

$$ P_0(te+y)=p(t):=t^\eta\prod_{j=1}^m(t^2-a_j^2). $$

Its $n$ roots are the distinct numbers $\pm j/n$, and also zero if $\eta=1$. Every two distinct roots are separated by at least $1/n$.

Let $\delta=1/(4n)$. Around every root $\rho$, take the interval $(\rho-\delta,\rho+\delta)$. These intervals are pairwise disjoint. Every endpoint has magnitude at most $1/2+1/(4n)\lt1$. At either endpoint, its distance from the root $\rho$ is $\delta$, and its distance from any other root is at least $1/n-\delta=3\delta$. Thus

$$ |p(\rho\pm\delta)|\geq\delta^n. $$

The two endpoint values have opposite signs: the factor $t-\rho$ changes sign, while each other factor keeps its sign throughout this interval. Lemma 1 and the choice of radius give

$$ |\varepsilon R_f((\rho\pm\delta)e+y)|\leq\varepsilon_n4^n=\frac12\delta^n. $$

So the perturbed polynomial keeps the baseline sign at every endpoint. By the intermediate value theorem it has a root inside each of the $n$ disjoint intervals. Its degree is at most $n$, and its leading coefficient is $P_{f,\varepsilon}(e)\gt0$, by homogeneity and Lemma 2. It therefore has degree exactly $n$ and precisely $n$ distinct real roots.

For any nonzero vector $y$ with zero coordinate sum, divide by $\lVert y\rVert_2$ and use homogeneity. For $y=0$ the line polynomial is $P_{f,\varepsilon}(e)t^n$. Finally, every $z$ has a unique decomposition $z=t_0e+y$ with zero coordinate sum for $y$. Replacing $t$ by $t+t_0$ proves the stated hyperbolicity assertion for every line parallel to $e$.

## Cone, stability, and signs

The positive orthant is connected, contains $e$, and has no zero of $P_{f,\varepsilon}$ by Lemma 2. It is therefore contained in the connected component of the nonvanishing set containing $e$. The hyperbolicity-cone theorem identifies this component with the hyperbolicity cone, and says that the polynomial is hyperbolic with respect to each point $b$ of that cone.

To check real stability directly from that theorem, let $a,b$ be real vectors with every coordinate of $b$ positive. Hyperbolicity in direction $b$ says that $s\mapsto P_{f,\varepsilon}(a+sb)$ has only real roots. In particular it is nonzero at $s=i$. Thus $P_{f,\varepsilon}(a+ib)\neq0$, which is precisely real stability.

At every Boolean vertex, $P_0(1,x)\gt0$ and $R_f(1,x)=f(x)$. Differentiating the logarithm gives the identity in the statement, and hence every prescribed strict sign table. $\blacksquare$

## Exact boundary for the main question

A product of admissible positive-coefficient linear factors belongs to the hyperbolic class. Replacing the factorization and its factorwise variations by arbitrary homogeneous hyperbolic polynomials and arbitrary polynomial variations discards a decisive constraint: the enlarged class already contains every Boolean sign direction at degree $n$.

This does not contradict the integer-factor rigidity theorem. The polynomial path above is not asserted to have all negative powers completely monotone. The preceding moment audit proves that imposing that condition would force linear factorization again. No head-complexity definition, target, or admissibility condition is modified here.

## Formal verification scope

`HyperbolicBooleanTangents.lean` proves `indicator_boolean`, `interpolate_boolean`, `indicator_homogeneous`, `interpolate_homogeneous`, `indicator_abs_le`, `interpolate_abs_le`, `perturbation_same_sign`, `root_in_open_interval`, and `splits_of_disjoint_brackets`. The latter proves that disjoint sign-changing intervals exhaust the roots of a real polynomial of bounded degree. The multivariate construction and the stability conclusion are the written proof above; no full Lean hyperbolicity theorem is asserted.
