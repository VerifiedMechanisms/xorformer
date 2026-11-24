# Positive Rational Interpolation Certificates

## Kernel-checked exact reduction

The module `formalization/HeadComplexity/Research/RationalBasisCapacity.lean` refines the earlier partially linear capacity reduction. It chooses an active basis before clearing denominators, so the selected actual score values are exactly $-1$ and $1$.

Write $N=2^n$, $L=nH+1$, and let $B_h(x)$ be a polynomial chart of denominators that are positive on the full Boolean cube. The normalized score has arbitrary real coefficients:

$$ S(x)=a_0+\sum_{h=1}^H\frac{\sum_{i=1}^n a_{h,i}x_i}{B_h(x)}. $$

The corresponding rational feature row is $F_x=(1,(x_i/B_h(x))_{h,i})$. Apply the compact polyhedron active-basis theorem to the inequalities $f(x)F_xa\geq1$ and a sufficiently large coefficient box. An extreme point has $L$ linearly independent active rows, chosen from $N$ actual sample rows and $2L$ coefficient-box rows. Actual rows interpolate their labels at the two levels $-1$ and $1$. A box row is $e_j$ or $-e_j$, with right side $-T$ for the convention used in `PartialLinearCertificate`.

Let $D_x=\prod_h B_h(x)$ and $P_x=D_xF_x$. Clear an actual basis row by multiplying both its matrix row and its right side by $D_x$. The actual-row right side is therefore $f(x)D_x$, not $f(x)$. Box rows retain their original matrix row and right side. Denote this polynomial matrix and right side by $M_c$ and $r_c$, where $c$ records the unordered basis and its selected labels. The polynomial extension score is

$$ Q_{c,x}=\det(M_c)\sum_j P_{x,j}\mathrm{cramer}(M_c,r_c)_j. $$

At a nonsingular positive chart point solving the basis equations, its exact value is

$$ Q_{c,x}=\det(M_c)^2D_xS(x). $$

Thus the full truth table is preserved. Define the chart class using denominator positivity, nonzero determinant, and the strict signs of these polynomials. The following declarations are checked by Lean:

- `HeadComplexity.RationalBasisCapacity.exists_certificate`: every represented truth table belongs to one such chart, with no head overhead.
- `HeadComplexity.RationalBasisCapacity.certificatePatterns_subset_represented`: every chart table is represented by the same positive rational denominator family.
- `HeadComplexity.RationalBasisCapacity.represented_eq_iUnion`: the union of the charts equals the represented class.
- `HeadComplexity.RationalBasisCapacity.card_represented_le_sum`: the cardinality of the represented class is at most the sum of these chart cardinalities.
- `HeadComplexity.RationalBasisCapacity.eq_constant_of_constant_sample_labels`: if the selected basis has only actual sample rows and all selected labels agree, the entire reconstructed truth table is constant.

The exact union is over

$$ \binom{N+2L}{L}2^L $$

certificates. The extra label bits on box rows are unused, so this harmless overcount can be retained. The coefficient-box radius is one additional real parameter. Positivity is retained on the whole cube, and no coefficient bound or margin hypothesis is imposed.

The earlier `DenominatorCapacity` count remains valid, but its active constraints were imposed on the already-cleared scores $D_xS(x)$. Its basis therefore fixes $S(x)=\pm1/D_x$, which discards the two-level interpolation structure above. Both reductions count unrestricted real coefficients; the new reduction isolates a stronger family for a possible improved estimate.

## A fixed-basis obstruction at one head

The following is a written proof, with separate finite exact checks. It is not claimed as a Lean cardinality theorem.

Let $n=m+k$ with $m,k\geq1$, and write inputs as $(x,z)\in\lbrace0,1\rbrace^m\times\lbrace0,1\rbrace^k$. Set $\alpha=1/(k+1)$. For each independent choice $r_i\in\lbrace0,\ldots,2^m-1\rbrace$, define

$$ B_r(x,z)=1+\sum_{j=0}^{m-1}(4\cdot2^j-2)x_j+\sum_{i=1}^k(4r_i+\alpha)z_i,\qquad S_r(x,z)=-1+\frac{\sum_{j=0}^{m-1}2(4\cdot2^j-1)x_j}{B_r(x,z)}. $$

All denominator slopes are strictly positive. Therefore the displayed affine ratio is one admissible original-model head by `FracAtom.ofPositiveAffineRatio`; the output bias is $-1$. The numerator slopes on the negative coordinates may be zero, which the original positive-affine-ratio compiler permits.

Every score has the same selected values on the basis consisting of the origin and all standard basis vectors:

$$ S_r(0,0)=-1,\qquad S_r(e_j,0)=1,\qquad S_r(0,e_i)=-1. $$

The rational feature matrix on these $n+1$ rows is nonsingular: subtract the origin row from each remaining row to obtain a diagonal matrix with positive diagonal entries $1/B_r(e_j)$, together with the bias pivot $1$. Thus this is one fixed actual-row interpolation certificate for every parameter choice.

The cleared score is

$$ P_r(x,z)=B_r(x,z)S_r(x,z)=-1+4\sum_{j=0}^{m-1}2^jx_j-4\sum_{i=1}^kr_iz_i-\alpha\sum_{i=1}^kz_i. $$

It never vanishes. If $\sum_i z_i=0$, it is an integer congruent to $-1$ modulo $4$. Otherwise its fractional part is nonzero because $0\lt\alpha\sum_i z_i\lt1$.

On the selector face $z=e_i$, write $s=\sum_j2^jx_j$. Then

$$ P_r(x,e_i)=4(s-r_i)-1-\alpha,\qquad P_r(x,e_i)\gt0 \Longleftrightarrow s\geq r_i+1. $$

Each value $r_i$ is therefore recovered from the truth table independently of the others. This one fixed basis has at least

$$ (2^m)^k=2^{mk} $$

strict truth tables. Taking $m=\lfloor n/2\rfloor$ gives exponent $\lfloor n^2/4\rfloor$.

Consequently a uniform per-basis bound $\exp(O(nH\log n))$ is false already at $H=1$. This obstruction is stronger than a multiple-fiber example with arbitrary real interpolation values: its selected sample values really are the fixed levels $-1$ and $1$, its denominator slopes have one admissible orientation, and its full cube scores are strict.

## Density-sensitive remaining lemma

The obstruction does not refute a near-critical-width theorem. A concrete possible bound, still unproved, is

$$ \log_2|\mathcal C_c|\leq CnH\left(\log_2 n+\log_2\frac{eN}{nH}\right),\qquad 1\leq nH\leq N/2, $$

where $\mathcal C_c$ is the exact positive rational certificate class defined above for normalized admissible affine denominators. Its second logarithm accommodates the one-head example. At $H\asymp N/n^{3/2}$ or $H\asymp N\log n/n^2$, both logarithms are $O(\log n)$, so the displayed upper bound and the certificate-selection entropy would be $o(N)$.

The first unproved step is the per-certificate estimate itself. A generic Warren bound on the Cramer polynomials has an additional factor comparable to $\log H$, and gives $O(n^2H)$ at the relevant widths. Positivity alone, separate convexity alone, and general real-value coordinate fibers have not supplied the needed replacement. Packing independent one-head examples by Boolean selector blocks uses about $\log H$ address coordinates, leaving only $O(\log n)$ data coordinates near the target width; that construction does not violate the proposed density-sensitive estimate.

No unrestricted asymptotic improvement is inferred from this reduction or counterexample. The original definition of `HeadComplexity.worstCaseHeadComplexity` is unchanged.
