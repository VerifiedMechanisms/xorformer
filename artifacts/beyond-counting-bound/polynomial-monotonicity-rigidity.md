# A Moment Audit of Homogeneous Polynomial Rigidity

## Statement and scope

Let $d\geq1$, let $e=(1,\ldots,1)\in\mathbb R^d$, and let $P$ be a homogeneous real polynomial of degree $H\geq1$ that is positive on $(0,\infty)^d$. The following four conditions are equivalent.

1. There are distinct vectors $w_1,\ldots,w_r$ in the simplex $\Delta=\lbrace w\in[0,\infty)^d:\sum_iw_i=1\rbrace$ and positive integers $m_1,\ldots,m_r$ such that $\sum_jm_j=H$ and $P(x)=P(e)\prod_j(w_j\cdot x)^{m_j}$.

2. Every negative power $P^{-\beta}$, with $\beta\gt0$, is completely monotone on the positive orthant.

3. There is a sequence of positive $\beta$ tending to zero for which $P^{-\beta}$ is completely monotone on the positive orthant.

4. The rational function $g=D_e\log P$ is completely monotone on the positive orthant.

Here complete monotonicity means that every mixed partial derivative of total order $k$ has sign $(-1)^k$, with zero allowed.

The factorization conclusion for homogeneous hyperbolic polynomials appears in [Wei, Corollary 7.5](https://arxiv.org/html/2609.31592v2). The proof below independently checks the positive-orthant case using a positive Laplace measure, homogeneity, and a polynomial square. It does not use that preprint's exponent-gap or Jordan-rigidity results. No claim of originality is made for the factorization theorem.

This theorem does not establish the head-complexity target. It explains exactly why the [real-exponent geometric construction](homogeneous-geometric-tangents.md) cannot be made polynomial while retaining arbitrary positive real factor weights.

## Proof

### Step 1. Infinitesimal powers give a completely monotone logarithmic derivative

Condition 2 implies condition 3. Suppose condition 3 holds. Fix a multi-index $\alpha$ of length $k$ and a coordinate $i$. Since $P^{-\beta}=\exp(-\beta\log P)$, differentiation with respect to $\beta$ at zero gives

$$ \lim_{\beta\downarrow0}\frac{\partial^{\alpha+e_i}P^{-\beta}(x)}{\beta}=-\partial^{\alpha+e_i}\log P(x). $$

The same limit holds along the sequence in condition 3. Complete monotonicity of those powers therefore implies

$$ (-1)^k\partial^{\alpha+e_i}\log P(x)\geq0. $$

Summing over $i$ proves condition 4. All differentiations here take place on an open set where $P\gt0$, so the expression is smooth jointly in $x$ and $\beta$ near $\beta=0$.

### Step 2. Homogeneity makes the Laplace measure radial

Assume condition 4. The Bernstein-Hausdorff-Widder-Choquet theorem gives a positive Borel measure $\mu$ on $[0,\infty)^d$ such that

$$ g(x)=\int e^{-y\cdot x}d\mu(y). $$

The Laplace transform determines this measure uniquely. These are the representation theorem and injectivity used in [Scott and Sokal, Theorem 2.2 and the discussion following it](https://people.maths.ox.ac.uk/scott/Papers/compmono.pdf).

Homogeneity of $P$ gives $g(sx)=s^{-1}g(x)$ for $s\gt0$. If $T_s(y)=sy$, then the Laplace transform of $(T_s)_\ast\mu$ is $g(sx)$. Uniqueness yields

$$ (T_s)_\ast\mu=s^{-1}\mu,\qquad \mu(sA)=s\mu(A). $$

The mass at zero is finite, since the Laplace integral is finite, and this scaling identity forces it to be zero.

For $y\neq0$, write $r=\sum_i y_i\gt0$ and $w=y/r\in\Delta$. Define a finite measure $\nu$ on $\Delta$ by

$$ \nu(B)=\mu\bigl(\lbrace y:0\lt\textstyle\sum_i y_i\leq1, y/(\sum_i y_i)\in B\rbrace\bigr). $$

Finiteness follows from $e^{-\sum_i y_i}\geq e^{-1}$ on this set. The scaling identity gives

$$ \mu\bigl(\lbrace y:a\lt\textstyle\sum_i y_i\leq b, y/(\sum_i y_i)\in B\rbrace\bigr)=(b-a)\nu(B) $$

for $0\leq a\lt b$. These rectangles determine the measure in radial coordinates, first on bounded radial intervals and then by countable union. Thus in those coordinates $d\mu=drd\nu(w)$. Tonelli's theorem and $w\cdot x\gt0$ give

$$ g(x)=\int_\Delta\int_0^\infty e^{-r(w\cdot x)}drd\nu(w)=\int_\Delta\frac{d\nu(w)}{w\cdot x}. $$

Euler's identity gives $g(e)=H$, and $w\cdot e=1$. Hence $\nu(\Delta)=H$.

### Step 3. A polynomial square bounds every projected support

Fix any $v\in\mathbb R^d$, and set $f_v(t)=P(e+tv)$. Its degree is at most $H$ and $f_v(0)=P(e)\gt0$. Over $\mathbb C$ write

$$ \frac{f_v(t)}{P(e)}=\prod_{j=1}^H(1+t\lambda_j), $$

including zero $\lambda_j$ when the degree is smaller than $H$. No reality of the $\lambda_j$ is assumed.

Euler's identity at $e+tv$ implies

$$ g(e+tv)=H-t\frac{f_v'(t)}{f_v(t)}=\sum_{j=1}^H\frac1{1+t\lambda_j}. $$

On the other hand the integral representation in Step 2 gives

$$ g(e+tv)=\int_\Delta\frac{d\nu(w)}{1+t(w\cdot v)}. $$

For sufficiently small $|t|$ both geometric-series expansions converge, and the integral expansion is uniform because $\Delta$ is compact and $\nu$ is finite. Comparing coefficients gives, for every $k\geq0$,

$$ \int_\Delta(w\cdot v)^k d\nu(w)=\sum_{j=1}^H\lambda_j^k. $$

Let

$$ q_v(s)=\frac{s^H f_v(-1/s)}{P(e)}=\prod_{j=1}^H(s-\lambda_j). $$

The expression on the left defines a monic real polynomial, including at $s=0$ by polynomial expansion. Applying the moment identity to the polynomial $q_v^2$ gives

$$ \int_\Delta q_v(w\cdot v)^2d\nu(w)=\sum_{j=1}^Hq_v(\lambda_j)^2=0. $$

The integrand is real and nonnegative. It follows that $q_v(w\cdot v)=0$ on the support of $\nu$: if it were nonzero at a support point, continuity would give an open neighborhood of positive measure where its square is bounded below by a positive constant. Consequently every projection of the support under $w\mapsto w\cdot v$ has at most $H$ points.

### Step 4. One separating projection makes the measure atomic

If the support of $\nu$ contained distinct points $w_1,\ldots,w_{H+1}$, choose $v$ outside the finitely many hyperplanes

$$ \lbrace v:(w_i-w_j)\cdot v=0\rbrace,\qquad i\neq j. $$

Such a $v$ exists, since a finite union of proper real linear hyperplanes cannot be all of $\mathbb R^d$. Then the $H+1$ projected values are distinct. Step 3 would make all of them roots of the polynomial of degree $H$ $q_v$, a contradiction.

Thus $\nu$ is supported at at most $H$ points. A finite Borel measure on the compact metric space $\Delta$ gives full measure to its support. For example, its complement is a countable union of open sets of measure zero, using a countable base. We may therefore write

$$ \nu=\sum_{j=1}^r a_j\delta_{w_j},\qquad a_j\gt0,\qquad \sum_{j=1}^r a_j=H. $$

### Step 5. Polynomial multiplicities make the masses integers

Choose $v$ so that the numbers $\rho_j=w_j\cdot v$ are nonzero and pairwise distinct. Again only finitely many proper hyperplanes are excluded. Steps 2 and 3 give an identity of rational functions of $t$:

$$ H-t\frac{f_v'(t)}{f_v(t)}=\sum_{j=1}^r\frac{a_j}{1+t\rho_j}. $$

At $t_j=-1/\rho_j$, the right-hand side has a simple pole with residue $a_j/\rho_j\neq0$. Therefore $t_j$ is a root of $f_v$. If its multiplicity is $m_j\geq1$, the residue of the left-hand side is $-t_jm_j=m_j/\rho_j$. Equality of residues yields $a_j=m_j$, a positive integer.

### Step 6. Recovering the polynomial

Define $Q(x)=\prod_j(w_j\cdot x)^{m_j}$. The preceding steps give

$$ D_e\log P(x)=\sum_j\frac{m_j}{w_j\cdot x}=D_e\log Q(x). $$

Thus $P(x+te)/Q(x+te)$ is constant for $t\geq0$, for every fixed positive $x$. Both polynomials have degree $H$, so as $t\to\infty$ this ratio tends to $P(e)/Q(e)=P(e)$. It follows that $P=P(e)Q$ on the positive orthant, hence as a polynomial identity. This proves condition 1.

Finally condition 1 implies condition 2 directly. For a nonzero vector $w\geq0$, any $\gamma\gt0$, and any multi-index $\alpha$ of length $k$,

$$ (-1)^k\partial^\alpha(w\cdot x)^{-\gamma}=(\gamma)_k\Bigl(\prod_iw_i^{\alpha_i}\Bigr)(w\cdot x)^{-\gamma-k}\geq0. $$

Products preserve complete monotonicity by the multivariate Leibniz rule. This completes the equivalence. $\blacksquare$

## Audit boundary for the head model

The measure argument retains the polynomial hypothesis throughout. In the real-exponent geometric construction, $g$ still has a positive atomic measure, but the weights need not be integers and there need not be a polynomial $q_v$ of bounded degree. Step 3 is precisely the missing condition there.

For a product of admissible affine denominators, the factorization is already given. Recovering it from complete monotonicity does not bound the number of Boolean sign tables of its varying tangent scores. That counting step is still a theorem-strength gap. No head-complexity definition or target statement is changed here.

`PolynomialMomentSupport.lean` checks the extension of power-moment identities to polynomials, square annihilation, and the consequent support bound. The Laplace representation, radial decomposition, atomicity in several variables, and full factorization theorem are written proofs only.
