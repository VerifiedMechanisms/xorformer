# Quadratic rank growth under reciprocal factorial homogenization

## Status and scope

This is a written proof, independently derived by the root and finite-count agents. The accompanying exact rational rank script corroborates small cases; it is not the proof. No Lean declaration is claimed here.

A length $q$ curvilinear inverse system can have a canonical reciprocal homogenization whose middle catalecticant rank is of order $q^2$. Thus there is no absolute constant $C$ that bounds the homogeneous border Waring rank of that canonical polynomial by $Cq$. A Boolean-grid version also rules out a constant-overhead exact-table compiler of this canonical polynomial into affine-product terms. These statements concern exact values and their limits. They do not rule out a compiler that changes the score while preserving its truth table, uses a positive multiplier, or only works near the critical original width.

## The curvilinear inverse system

For an integer $m\geq1$, let $q=2m+1$ and define

$$ F_m(X,Y)=[t^{2m}]\exp(Yt+Xt^2)=\sum_{j=0}^{m}\frac{X^jY^{2m-2j}}{j!(2m-2j)!}. $$

Its derivative-closed vector space has dimension exactly $q$. Indeed, differentiation by $X$ agrees with differentiation twice by $Y$. Every derivative is therefore in the span of

$$ F_m,\partial_YF_m,\ldots,\partial_Y^{2m}F_m. $$

These $2m+1$ polynomials are linearly independent: after setting $X=0$, they become nonzero multiples of the distinct monomials $Y^{2m},Y^{2m-1},\ldots,1$. Equivalently, the apolar algebra is the curvilinear algebra $\mathbb R[t]/(t^{2m+1})$, with the operators $\partial_Y$ and $\partial_X$ acting as $t$ and $t^2$.

The corresponding reciprocal coefficient is

$$ [t^{2m}]\frac1{B+Yt+Xt^2}=\frac{P_m(B,X,Y)}{B^{2m+1}},\qquad P_m(B,X,Y)=\sum_{j=0}^{m}(-1)^j\binom{2m-j}{j}B^jX^jY^{2m-2j}. $$

The coefficient formula follows by expanding the geometric series. A term using $j$ copies of $Xt^2$ uses $2m-2j$ copies of $Yt$, hence $2m-j$ copies of the nonconstant denominator part. The sign is $(-1)^{2m-j}=(-1)^j$. The polynomial $P_m$ is homogeneous of ordinary degree $2m$ in $B,X,Y$.

## Full middle catalecticant rank

Index rows and columns by triples of nonnegative integers summing to $m$. For row $\alpha=(a,b,c)$ and column $\beta=(d,e,f)$, use the scalar entry

$$ C_{\alpha,\beta}=\partial_B^{a+d}\partial_X^{b+e}\partial_Y^{c+f}P_m. $$

The entry is zero unless $a+d=b+e=j$. In the latter case it equals

$$ C_{\alpha,\beta}=(-1)^j(j!)^2(2m-2j)!\binom{2m-j}{j}=(-1)^j j!(2m-j)!. $$

Group rows by $\delta=a-b$ and columns by the opposite difference $d-e=-\delta$. Every other block vanishes. The paired row and column groups have the same size.

For $\delta\geq0$, write the rows as

$$ (a,b,c)=(b+\delta,b,m-2b-\delta),\qquad 0\leq b\leq\left\lfloor\frac{m-\delta}{2}\right\rfloor, $$

and the columns as $(d,e,f)=(s,s+\delta,m-2s-\delta)$ in the same range for $s$. Multiplying rows and columns by signs removes $(-1)^{b+s+\delta}$. The resulting block is the Hankel matrix

$$ H_{b,s}=(b+s+\delta)!(2m-b-s-\delta)!. $$

Negative $\delta$ gives the same statement after exchanging $B$ and $X$.

### Strict positivity of every block

The factorial entries have the integral representation

$$ H_{b,s}=(2m+1)!\int_0^{\infty}\frac{u^{b+s+\delta}}{(1+u)^{2m+2}}du. $$

The identity follows from the substitution $v=u/(1+u)$ and the beta-integral identity, itself proved by integration by parts. All exponents in this finite block lie in the integrable range.

For a nonzero real vector $(z_b)$, its quadratic form is

$$ z^{\top}Hz=(2m+1)!\int_0^{\infty}\frac{u^{\delta}\left(\sum_bz_bu^b\right)^2}{(1+u)^{2m+2}}du\gt0. $$

The polynomial in the square is nonzero, and hence is nonzero on some open subinterval of $(0,\infty)$. The other factors are strictly positive there. This proves strict positive definiteness, and therefore nonsingularity, of every block. After the column permutation and sign changes, the full catalecticant is a direct sum of these nonsingular blocks. Consequently

$$ \mathrm{rank}C=\binom{m+2}{2}. $$

A pure power of a linear form has catalecticant rank at most one. A sum of $K$ pure powers has rank at most $K$, and this inequality persists under coefficientwise limits because every $(K+1)$-minor vanishes. Thus both real and complex homogeneous border Waring rank satisfy

$$ \underline{\mathrm{rank}}_{\mathrm W}(P_m)\geq\binom{m+2}{2}=\frac{(q+1)(q+3)}8. $$

The ratio to the local-algebra length $q$ is unbounded. This refutes the proposed constant-factor canonical homogenization lemma already for curvilinear algebras.

## An exact Boolean-table consequence

The same rank obstruction can be transferred to finite Boolean observations, without treating arbitrary linear observations as actual cube rows.

Let $L=\lceil\log_2(2m+1)\rceil$. Partition $n=6L$ Boolean variables into two sides, and on each side use three blocks of $L$ variables to encode three independent integers in $\lbrace0,\ldots,2^L-1\rbrace$. Denote the sums of the two encodings by $U,V,W$. Set

$$ B=1+U+V+W,\qquad X=-1-V,\qquad Y=1+W. $$

Every slope of $B$ is strictly positive. The affine coordinate change from $(U,V,W)$ to $(B,X,Y)$ is invertible. Consider the table $P_m(B,X,Y)$ and its matrix flattening between the two sides of the Boolean partition.

Evaluation on a Cartesian grid with at least $2m+1$ points in each coordinate is injective on polynomials having degree at most $2m$ in each coordinate. Therefore the flattening has the same rank as the coefficient matrix of the polynomial in the two triples of encoding variables. Independent invertible affine coordinate changes on each side preserve that coefficient-matrix rank. The submatrix pairing homogeneous degree $m$ on each side is the catalecticant above, up to nonzero row and column factorial factors. Hence the Boolean flattening rank is at least $\binom{m+2}{2}$.

An affine-product term on the Boolean cube has the form

$$ (a_0+\sum_{i=1}^n a_ix_i)\prod_{i=1}^n(u_i+v_ix_i). $$

Across the chosen partition, its affine factor splits into a function of the first side plus a function of the second. Its flattening rank is therefore at most two. A sum of $K$ such terms has flattening rank at most $2K$, including in pointwise limits on the finite cube. Any exact-table or border exact-table representation of this canonical polynomial consequently needs

$$ K\geq\frac12\binom{m+2}{2}. $$

The local reciprocal jet is obtained from $q=2m+1$ genuine heads by finite differences at denominator paths $B+Yt+Xt^2$. For sufficiently small real $t$, all denominator coefficients remain strictly positive because those of $B$ are strictly positive. Arbitrary signed finite-difference coefficients are allowed in the original model. This confirms that the example lies within the permitted local degeneration geometry.

There is an especially direct warning about scope: for the displayed Boolean substitution, $B\gt0$, $X\lt0$, and $Y\gt0$. Every summand of $P_m$ is then positive. Its truth table is constant, despite the large exact-table rank. Thus this example gives no lower bound on the number of heads needed for its labels and does not disprove the desired unrestricted repair theorem.

## The remaining access question

A possible route may still change the positive multiplier, alter the polynomial within its strict sign cell, or permit more than constant overhead in a way that is affordable only at critical widths. The failed lemma is precise: the canonical map from a length $q$ local inverse system to its positively cleared reciprocal score does not preserve homogeneous border Waring rank, or exact Boolean affine-product border rank, within a universal constant factor. Any repair using that map must supply an additional sign-preserving modification or a different counting argument.
