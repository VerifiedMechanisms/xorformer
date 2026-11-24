# A weighted-degree sign-count theorem

## Status and scope

This note proves a sign-count bound that charges each parameter according to its positive integer weight. The proof uses ordinary isolated-root Bezout and Sard's theorem. No weighted intersection theory is needed. It can remove a factorial degree penalty for suitably distributed jet parameters, but it does not supply the missing parameterization of unrestricted affine-ratio scores.

This is a written proof, independently derived and checked in discussion with the root agent. It has not been formalized in Lean.

## Theorem

Let $f_1,\ldots,f_m$ be real polynomials in $p\geq1$ real variables $z_1,\ldots,z_p$. Give variable $z_\ell$ a positive integer weight $w_\ell$. Suppose $D$ is a positive integer, $w_\ell\leq D$ for every $\ell$, and every monomial of every $f_i$ has weighted degree at most $D$. Let $T$ be the number of strict sign vectors realized by these polynomials. Then

$$ T\leq\frac{\prod_{\ell=1}^p(4D-w_\ell)}{\prod_{\ell=1}^p w_\ell}\sum_{j=0}^p\left(\frac23\right)^j\binom mj. $$

In particular, when $p\leq m$,

$$ T\leq\frac{1}{\prod_{\ell=1}^p w_\ell}\left(\frac{8eDm}{p}\right)^p. $$

Binomial coefficients with $j\gt m$ are interpreted as zero. Only strict signs are counted.

## Proof

### Step 1. Smooth shifted sign regions

Choose one witness for every realized strict sign vector. There are finitely many witnesses. Choose a positive threshold vector $\varepsilon=(\varepsilon_1,\ldots,\varepsilon_m)$ small enough that every sign vector still has a witness satisfying $\sigma_i f_i(z)\geq\varepsilon_i$ for all $i$.

Choose these thresholds generically. By Sard's theorem, simultaneously for every index subset $I$ of size at most $p$ and every threshold sign assignment $\tau$, the equality variety

$$ V_{I,\tau}=\lbrace z:f_i(z)=\tau_i\varepsilon_i\text{ for all }i\in I\rbrace $$

is empty or smooth of codimension $|I|$. No $p+1$ equalities hold simultaneously. To justify the simultaneous choice, each exceptional target set is null by Sard; taking its inverse image under a coordinate projection preserves nullity in the bounded threshold box. There are only finitely many choices. The same argument for subsets of size $p+1$ makes their fibers empty, since every value in the image of a map from $\mathbb R^p$ to $\mathbb R^{p+1}$ is critical.

### Step 2. A coercive weighted objective

Put $a_\ell=\lceil D/w_\ell\rceil$ and define

$$ Q_0(z)=\sum_{\ell=1}^p z_\ell^{2a_\ell},\qquad Q_u(z)=Q_0(z)-\sum_{\ell=1}^p u_\ell z_\ell. $$

Every exponent is even and at least two. Thus $Q_u$ is coercive for every $u\in\mathbb R^p$.

For a fixed nonempty smooth $V_{I,\tau}$ with $j=|I|$, consider the smooth map on its normal-bundle coordinates

$$ (z,\lambda)\longmapsto\nabla Q_0(z)-\sum_{i\in I}\lambda_i\nabla f_i(z). $$

Its domain has dimension $(p-j)+j=p$. Sard's theorem permits one common vector $u$ that is a regular value for all of the finitely many such maps. This also covers the empty active set.

For each realized sign vector $\sigma$, the closed set

$$ K_\sigma=\lbrace z:\sigma_i f_i(z)\geq\varepsilon_i\text{ for every }i\rbrace $$

is nonempty. Coercivity gives a minimizer of $Q_u$ on $K_\sigma$. Its active set $I$ has size at most $p$. Active gradient independence gives unique multipliers satisfying the square KKT system

$$ f_i(z)=\tau_i\varepsilon_i\quad(i\in I),\qquad \partial_{z_\ell}Q_0(z)-u_\ell=\sum_{i\in I}\lambda_i\partial_{z_\ell}f_i(z)\quad(1\leq\ell\leq p). $$

The regular-value choice of $u$ makes the Jacobian of this square system invertible at the chosen root. Indeed, a vector in its kernel first has its $z$ component tangent to $V_{I,\tau}$, and then lies in the kernel of the derivative of the displayed normal-bundle map. That derivative is an isomorphism at a regular preimage. Thus the selected real root is nonsingular and isolated over the complex numbers too.

Each selected point determines its entire sign vector because every evaluation there has nonzero absolute value at least its threshold. Consequently different sign vectors give different selected points.

### Step 3. Weighted isolated-root bound using an ordinary power map

The following elementary consequence of ordinary affine Bezout will be used. For a square system in $r$ variables of positive integer weights $v_1,\ldots,v_r$, suppose equation $k$ has weighted degree at most $d_k$. Any finite collection of distinct nonsingular roots has cardinality at most

$$ \frac{\prod_{k=1}^r d_k}{\prod_{k=1}^r v_k}. $$

To prove this, first translate every original coordinate by a generic constant so that none of the finitely many chosen root coordinates is zero. Translation cannot increase weighted degree, because it only replaces a monomial by monomials with coordinatewise smaller exponents. Substitute the power map $z_\ell=y_\ell^{v_\ell}$. Every resulting equation has ordinary degree at most its weighted-degree bound. Each chosen root now lifts to exactly $\prod_\ell v_\ell$ distinct complex roots. These roots are nonsingular because the power-map Jacobian is invertible away from zero coordinates. Ordinary affine Bezout bounds their number by $\prod_k d_k$, proving the claim. Other roots or positive-dimensional components do not affect the bound on these isolated roots.

### Step 4. Apply the bound to KKT systems

Give the original variables their weights $w_\ell$, and give each multiplier weight $3D$. The $j$ constraint equations have weighted degree at most $D$.

For the stationarity equation in coordinate $z_\ell$, the multiplier term has weighted degree at most $3D+(D-w_\ell)=4D-w_\ell$. Its objective derivative has weighted degree

$$ (2\lceil D/w_\ell\rceil-1)w_\ell\leq2D+w_\ell\leq4D-w_\ell, $$

where the last inequality uses $w_\ell\leq D$. The constant term has degree zero. Thus the weighted isolated-root estimate gives at most

$$ \frac{D^j\prod_{\ell=1}^p(4D-w_\ell)}{(3D)^j\prod_{\ell=1}^p w_\ell}=\frac{\prod_{\ell=1}^p(4D-w_\ell)}{3^j\prod_{\ell=1}^p w_\ell} $$

selected roots for each active set and threshold sign assignment. There are $\binom mj$ active index sets and $2^j$ assignments. Summing proves the first estimate.

For the simpler estimate, use $4D-w_\ell\leq4D$ and

$$ \sum_{j=0}^p(2/3)^j\binom mj\leq\sum_{j=0}^p2^j\binom mj\leq\left(\frac{2em}{p}\right)^p. $$

For the last inequality, put $t=p/(2m)\leq1$ and bound the truncated sum by $t^{-p}(1+2t)^m$. This completes the proof. $\blacksquare$

## What a factorial cancellation actually requires

Suppose $q$ variables occur at each weight $1,2,\ldots,K+1$, and another $r$ variables have weight one. Then $p=q(K+1)+r$ and

$$ \prod_\ell w_\ell=((K+1)!)^q. $$

If the weighted degree is at most $a(K+1)$ for a fixed $a$, the factorial estimate $(K+1)!\geq((K+1)/e)^{K+1}$ absorbs the factor $D^{q(K+1)}$ up to an exponential in the number of those variables. Only the extra weight-one block retains a factor of order $(K+1)^r$.

That last qualification is essential. A common-base curved denominator germ has many first-order directions $C_{h,1}$ and constant numerator coefficients $A_{h,0}$. These form a weight-one block of order $nH$. If its first decisive score coefficient has order $K$, merely applying this theorem can still cost order $nH\log K$ on that block. Adding all higher jets spreads weights but naively introduces order $nHK$ variables instead of order $nH$.

For example, the coefficient of order $k$ of

$$ \frac{\sum_{j\geq0}A_j t^j}{B_0+\sum_{j\geq1}C_jt^j} $$

becomes a polynomial after multiplication by $B_0^{k+1}$. Assigning weight one to the coefficients of $B_0$, and weight $j+1$ to those of $A_j$ and $C_j$, gives weighted degree exactly at most $2k+1$. This is favorable degree bookkeeping, but it does not remove the many low-weight first-direction variables when there are many heads.

No theorem here turns an arbitrary original-model representation into a jet parameterization whose weighted variable distribution achieves the required saving. Fixed radial exponential transfer supplies such a cancellation-independent compiler in its restricted setting; extending that mechanism to general curved or finite-scale configurations remains unresolved.
