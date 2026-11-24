# Every one-head truth table has a quantitative same-width repair

## Statement and status

Let $n\geq1$ and put $d=n+1$. Every Boolean truth table represented by at most one original unrestricted head has a representation by one admissible head, with zero bias and relative full-cube amplitude margin at least

$$ d^{-(d/2+2)}=(n+1)^{-(n+5)/2}. $$

The new denominator is always $1+\sum_i x_i$. Its numerator has integer coefficients of absolute value at most $d^{d/2}$. Thus the repair changes the denominator direction if necessary and permits every original real coefficient and cancellation with the original bias.

The sharper displayed constant is a written proof using Hadamard's determinant inequality. A factorial variant is kernel checked in `HeadComplexity/Research/IntegerSeparatorMarginRepair.lean`: every such truth table has a genuine one-head repair with margin at least

$$ \frac{1}{(n+1)^2(n+1)!}. $$

The exact declarations are `HeadComplexity.IntegerSeparatorMarginRepair.exists_bounded_integer_separator`, `exists_bounded_integer_affine`, `hasRelativeMargin_of_isLTF`, `one_head_repair`, and `repair_of_HStar_le_one`. The last two use the original `computableWithHeadsN` and `HStar` definitions. The formalization proves the active-row existence and Cramer steps, uses the elementary Leibniz bound $|\det R_i|\leq d!$, and constructs the original admissible head with its full-cube norm bound. The transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`. The theorem gives no repair bound at unbounded head count.

## Reduce the target to a strict affine separator

An original score with one head has the form

$$ S(x)=b+\frac{A(x)}{B(x)}=\frac{bB(x)+A(x)}{B(x)},\qquad B(x)\gt0. $$

The numerator on the right is affine. For the original classifier convention, first shift the bias slightly to make the entire finite sign table strict, as justified by `exists_strict_fracCertificate` in `Atoms/ClearedNormalForm.lean`. This keeps the width unchanged. If the original width is zero, the table is constant and is also a strict affine threshold.

Consequently, after identifying the labels with $F(x)\in\lbrace-1,+1\rbrace$, there is a real vector $w\in\mathbb R^d$ such that

$$ F(x)\langle(1,x_1,\ldots,x_n),w\rangle\gt0 $$

at every cube vertex. Scaling this vector by a positive constant gives all these signed products at least one.

## An elementary bounded integer separator

Write $r_x=F(x)(1,x_1,\ldots,x_n)$ and consider the feasible polyhedron

$$ P=\lbrace w\in\mathbb R^d:\ \langle r_x,w\rangle\geq1\text{ for every }x\rbrace. $$

It is nonempty. Its constraint rows span $\mathbb R^d$: before multiplication by the signs, the rows at zero and at the $n$ singleton vertices already span, and changing row signs preserves their span.

There is a point of $P$ with $d$ linearly independent active rows. Here is a direct finite argument. Start at any feasible point. If the span of its active rows has dimension below $d$, choose a nonzero vector $v$ annihilating those rows. Some constraint row has a nonzero product with $v$, by the spanning property. Replace $v$ by $-v$ if needed so at least one such product is negative. Move along $w+tv$ for positive $t$, stopping at the first new active constraint. The stopping time is the minimum of the finitely many positive ratios

$$ \frac{\langle r_x,w\rangle-1}{-\langle r_x,v\rangle} $$

over the rows having negative denominator product. Each numerator in this minimum is positive because an active row annihilates $v$. Hence the time is positive and finite. Old active constraints remain active, all constraints remain feasible, and a newly active row is outside their former span because its product with $v$ is nonzero. Repeat. The rank increases each time, so this process stops after at most $d$ steps.

Choose $d$ independent active rows and place them in the integer matrix $R$. All its entries lie in $\lbrace-1,0,1\rbrace$, its determinant is a nonzero integer, and the selected feasible point satisfies $Rw=\boldsymbol1$. Cramer's rule gives

$$ w_i=\frac{\det R_i}{\det R}, $$

where $R_i$ replaces column $i$ by the all-ones column. Define the integer vector

$$ a_i=\mathrm{sign}(\det R)\det R_i. $$

Then $a=|\det R|w$, so every signed cube evaluation of $a$ is at least $|\det R|\geq1$. Each row of $R_i$ has Euclidean norm at most $\sqrt d$. Hadamard's determinant inequality gives

$$ |a_i|=|\det R_i|\leq d^{d/2}. $$

This proves the quantitative integer separator without any assumption on the height of the starting real coefficients.

## Convert it to one admissible head

Let $A_a(x)=a_0+\sum_i a_i x_i$, and choose

$$ \phi(x)=\frac{A_a(x)}{1+\sum_i x_i}. $$

The denominator has positive constant coefficient and strictly positive slopes. The constructor `FracAtom.ofPositiveAffineRatio` therefore realizes this ratio by one original admissible head, with no numerator sign restriction.

Its full-cube norm is at most $d^{d/2+1}$, since the denominator is at least one and the numerator has at most $d$ terms. Its smallest signed value is at least $1/d$, since the integer signed numerator is at least one and the denominator is at most $d$. The ratio of these quantities is at least $d^{-(d/2+2)}$, as asserted.

## Extension and the first scaling gap

The same theorem repairs any number of heads whose denominators are all positive scalar multiples of one common affine denominator. Their numerators and bias combine into one affine numerator. In fact, this class compresses to one head before the quantitative repair.

For several genuinely different denominators, fixing them still makes the numerator parameters linear. The analogous active-row matrix, however, has entries containing the target-dependent reciprocals $1/B_h(x)$. Its nonzero determinants need not have any universal lower bound. The fixed-pencil and full-rank boundary examples in this directory show that optimizing all numerator parameters cannot remove this problem while the denominators are retained.

Thus the scalable ingredient in the one-head proof is not merely linear optimization. It is that the sign table can be moved into a *fixed integer feature matrix* of dimension $n+1$, with no head overhead. At width $H$, one would need an admissible sign-preserving replacement whose integer feature certificate has controlled dimension and height, while keeping at most a constant times $H$ heads. No such replacement is established here.

The root agent independently audited the written active-row argument, integer determinant hypotheses, original admissibility construction, and full-cube margin calculation before this checkpoint.
