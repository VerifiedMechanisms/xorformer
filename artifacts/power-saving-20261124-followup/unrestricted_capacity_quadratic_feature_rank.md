# Generic rank of quadratic reciprocal features

## Statement and status

Let $n\geq2$, $N=2^n$, and $d=\binom n2$. Define

$$ H_0=\left\lceil\frac N d\log d\right\rceil+\left\lceil\frac N d\right\rceil. $$

For every $H\geq H_0$, fix arbitrary ordered pairs of cube vertices $(p_h,q_h)$, with repetition permitted. Let $B_h$ range independently over affine forms with strictly positive constant and variable coefficients. For each head consider the real functions

$$ x\longmapsto\frac{Q(x)}{B_h(x)^2},\qquad \deg Q\leq2,\qquad Q(p_h)=Q(q_h)=0. $$

On a nonempty Zariski-open subset of this strictly positive parameter cone, their joint evaluation span has dimension at least $N-2$. Without the two endpoint-zero conditions, the corresponding generic rank is exactly $N$ under the same head budget.

This is a written proof, independently checked by the finite-margin audit agent. It is not a kernel-checked declaration or an unrestricted capacity bound. The rank statement concerns actual coordinate evaluations on the full Boolean cube and admissible positive denominator coefficients. An intermediate degeneration below is only a witness that a polynomial minor is nonzero.

## Covering all but two rows

For a center $c$, let $S_c$ be its Hamming sphere of radius exactly two. Every sphere contains $d$ vertices, and every cube vertex belongs to exactly $d$ such spheres.

Use the heads in their prescribed order. If $U$ is the current uncovered set, averaging over all centers gives

$$ \frac1N\sum_c|S_c\cap(U\setminus\lbrace p_h,q_h\rbrace)|=\frac dN|U\setminus\lbrace p_h,q_h\rbrace|\geq\frac dN(|U|-2). $$

Choose a center attaining at least this average and cover the indicated rows. As long as more than two rows remain, the uncovered count satisfies

$$ |U_{h+1}|-2\leq\left(1-\frac dN\right)(|U_h|-2). $$

After $k=\lceil(N/d)\log d\rceil$ steps, at most $N/d+2$ rows remain, using $1-a\leq e^{-a}$. If $d=1$, take $k=0$ and this conclusion already holds. Every further head covers at least one row while more than two remain: choose any uncovered vertex different from its two prescribed endpoints, then choose a center at distance two from that vertex. The next $\lceil N/d\rceil$ heads therefore leave at most two rows uncovered.

Assign each covered row to one head that covered it. No row assigned to head $h$ equals either of its prescribed endpoints.

## Quadratic interpolation on a pole sphere

Fix one selected center $c$. Write $y_i=x_i$ when $c_i=0$ and $y_i=1-x_i$ when $c_i=1$. Put

$$ L_c(x)=\sum_i y_i-2. $$

For a selected row on $S_c$, let $i,j$ be its two changed coordinates. The quadratic $Q_0=y_i y_j$ is one at that row and zero at every other row of $S_c$.

We can impose the two endpoint-zero conditions without changing these sphere values. Endpoints already on the sphere have $Q_0=0$, because neither is the selected row. For each endpoint $z$ off the sphere, prescribe an affine form $R$ to have value $Q_0(z)/L_c(z)$. An affine form interpolates arbitrary values at at most two distinct vertices: if two vertices differ, use one coordinate on which they differ. Repeated endpoints require only one condition. Then

$$ Q=Q_0-L_cR $$

has degree at most two, vanishes at both prescribed endpoints, and still isolates the selected row on its sphere.

## From a degeneration to generic admissible rank

For the chosen center of each head, temporarily use

$$ B_{h,\varepsilon}=L_{c_h}+\varepsilon. $$

Take $0\lt\varepsilon\lt1/2$. Every denominator is nonzero at every cube vertex, although these temporary denominators need not be positive or coherently oriented. For each selected row and its quadratic from the preceding paragraph,

$$ \varepsilon^2\frac{Q(x)}{B_{h,\varepsilon}(x)^2}\longrightarrow\mathbf1_{\lbrace x=x_{\mathrm{selected}}\rbrace}. $$

Indeed, on the pole sphere the denominator is exactly $\varepsilon$ and $Q$ isolates the row. Off that sphere, the denominator tends to a nonzero integer. The selected rows and columns therefore have an evaluation minor whose scaled determinant tends to one. In particular this rational minor is not identically zero.

After clearing its denominator, its numerator is a nonzero polynomial in all affine denominator coefficients. A nonzero real polynomial cannot vanish on an open set. Consequently this minor is nonzero on a nonempty Zariski-open subset of the strictly coefficient-positive cone. Those denominator forms are genuine admissible positive affine denominators in the original model. This proves rank at least $N-2$ there.

For the unconstrained statement, omit endpoint removal and endpoint interpolation. The greedy recurrence starts at $|U|$ instead of $|U|-2$, and the same budget covers every row. The pole-sphere quadratics give a full $N$ by $N$ nonzero minor.

## Relation to the duplication calculation

The budget satisfies $H_0=O(N\log n/n^2)$. Thus at the proposed power-saving width $cN/n^{3/2}$, for every fixed $c\gt0$ and sufficiently large $n$, generic quadratic reciprocal features already have almost full row rank.

At a regular duplicated margin optimum, the written Hessian calculation in `unrestricted_capacity_two_extrema.md` gives a common signed dual measure annihilating every endpoint-zero quadratic feature. The rank theorem says that the space of such annihilating measures generically has dimension at most two. It does not prove that the measure is zero, that its labels have small entropy, or that a width-preserving improvement exists. First-order and endpoint-corrected second-order equations impose additional conditions, but no required entropy bound for their solution set has been established.

Genericity is essential. For example, take arbitrarily many distinct strictly positive denominators

$$ B_h(x)=1+c_h\sum_i x_i,\qquad c_h\gt0. $$

On each Hamming layer, division by each $B_h^2$ is only multiplication by a scalar. The entire unconstrained feature span consequently has dimension at most

$$ (n+1)\left(1+n+\binom n2\right), $$

regardless of the number of distinct poles. This is exponentially smaller than $N$ for large $n$. Such shared-statistic configurations are covered by separate restricted counting theorems, but no theorem classifies every deficient configuration that way.

The precise next requirement is a model-specific entropy bound for the exceptional denominator configurations or for the signed dual solutions of the full endpoint-corrected system. Merely observing a nonzero generic minor gives no useful bound on the degree, codimension, or number of sign cells of that exceptional locus. The unrestricted margin-repair and capacity gaps remain open.
