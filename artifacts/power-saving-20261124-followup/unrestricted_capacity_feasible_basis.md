# Globally Feasible Rational Basis Certificates

## Exact unrestricted embedding

`formalization/HeadComplexity/Research/FeasibleRationalBasis.lean` retains the full active-polyhedron conditions that the earlier rational interpolation charts dropped. The original strict truth table is first normalized to positive affine denominators and arbitrary linear numerator coefficients. It is then scaled to signed score at least one, and an extreme point is selected inside a sufficiently large coordinate box.

For $L=nH+1$, each certificate records $L$ unordered rows from the $N$ actual cube samples and $2L$ coordinate-box rows, together with their selected labels. As in `RationalBasisCapacity`, actual rows are cleared only after the active basis is selected. Their right sides are their labels times the common denominator, so their original score values are exactly $-1$ or $1$.

The coefficients are reconstructed uniquely by Cramer's rule. In addition to positive denominators and a nonsingular basis, the chart now retains

$$ f(x)S(x)\geq1\quad\text{for every cube input }x,\qquad |a_j|\leq T\quad\text{for every linear coefficient }j. $$

Here $f(x)$ is interpreted as $-1$ or $1$. The only free continuous variables are the denominator parameters and the scalar box radius $T$; the numerator coefficients are the specified Cramer expressions. The denominator parameters remain target-dependent arbitrary real numbers, and every signed cancellation remains allowed.

The following declarations are kernel checked:

- `HeadComplexity.FeasibleRationalBasis.exists_bounded_active_basis` retains the entire coordinate box in the compact-polyhedron basis theorem.
- `HeadComplexity.FeasibleRationalBasis.exists_unsigned_basis` retains unit signed slack on every input, the box, the unsigned selected rows, and nonsingularity.
- `HeadComplexity.FeasibleRationalBasis.exists_certificate` proves that every strict positive rational representation enters a globally feasible chart.
- `HeadComplexity.FeasibleRationalBasis.represented_eq_iUnion` proves an exact union for the positive rational chart family.
- `HeadComplexity.FeasibleRationalBasis.exists_certificate_of_computable` starts directly from the unchanged `computableWithHeadsN n H f` definition.
- `HeadComplexity.FeasibleRationalBasis.card_headComputableFunctions_le_sum` bounds the original model's truth-table count by the sum of the globally feasible chart counts.

The original-model chart uses exactly $nH$ denominator slope variables:

$$ B_h(x)=1+\sum_{i=1}^n b_{h,i}x_i. $$

The count still has exactly $\binom{N+2L}{L}2^L$ discrete certificates. No margin lower bound or numerator-size bound independent of the chosen $T$ is assumed.

## Admissibility scope

The formal chart is an upper-count enlargement: it contains all positive affine denominators, not only the two coherent slope orientations of a genuine original head. Its embedding from the original model is unconditional and does not add heads. An upper bound on this enlarged chart family would therefore give a valid lower bound for the original model.

Changing numerator coefficients over a strictly positive- or strictly negative-slope admissible denominator preserves admissibility. A constant-denominator original head has additional numerator restrictions, so the reverse chart inclusion is a statement about the positive rational enlargement, not an asserted original-head compiler. An actual-head repair would need to handle that case, for example by a separately justified positive-slope perturbation preserving finite strict signs before selecting the active basis. No such repair is used to claim a lower bound here.

## Why the global constraints cannot be omitted

The one-head family in `unrestricted_capacity_rational_basis.md` supplies exponentially many tables for a fixed two-level interpolation basis, but it generally has other scores inside $(-1,1)$. It therefore does not disprove a stronger upper bound for the globally feasible chart.

Even checking only a selected set of actual Boolean inputs is insufficient. Consider the following two one-head scores on three bits:

$$ S_1(x,y,z)=\frac{-3+9x+y-z}{1+x+y+3z},\qquad S_2(x,y,z)=\frac{-7+5x+3y+5z}{1+x+3y+z}. $$

Both denominators have strictly positive coefficients. On the same affine basis of four actual cube points, they have identical unit-level values:

$$ \begin{array}{c|rrrr} (x,y,z)&(0,0,1)&(0,1,0)&(1,0,1)&(1,1,1)\cr S_1,S_2&-1&-1&1&1\end{array} $$

Their extension values at $(1,0,0)$ disagree while satisfying unit slack:

$$ S_1(1,0,0)=3,\qquad S_2(1,0,0)=-1. $$

Thus the five-point subset admits two feasible extensions with the same selected basis. On the omitted cube point $(0,1,1)$, however,

$$ S_1(0,1,1)=-\frac35,\qquad S_2(0,1,1)=\frac15, $$

so both fail the full-cube condition. These are exact rational identities, not numerical approximations. The whole Boolean cube, including its missing edges and faces, is a substantive hypothesis.

## The remaining estimate

A sufficient estimate would bound each globally feasible chart, or their average, by

$$ \log_2|\mathcal C_c|\leq CnH\left(\log_2 n+\log_2\frac{eN}{nH}\right) $$

in the near-critical width regime. Together with the existing finite certificate count, this would be substantially stronger than the requested benchmark. No such estimate has been proved. Generic polynomial sign counting of the reconstructed scores still costs $O(n^2H)$ at those widths.

The next structural question is whether full-cube unit feasibility forces stronger restrictions on the possible extensions than positivity and two-level interpolation alone. At one head, writing the score as $P/B$ gives the exact condition $|P(x)|\geq B(x)$ on every vertex. For positive denominator coefficients, this is an empty interval around zero for every Boolean subset sum of the numerator coefficients. A proof at one head would be an intermediate rigidity result, not an unrestricted many-head capacity theorem.
