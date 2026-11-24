# A quantitative repair for arbitrary Hamming-direction poles

## Statement and scope

Let $n\geq1$ and $d=n+1$. Consider a strict original-model truth table represented by any finite score whose denominators depend only on Hamming weight. Thus every denominator is

$$ B_h(x)=a_h+b_h|x|,\qquad a_h+b_hk\gt0\quad(0\leq k\leq n), $$

while every numerator is arbitrary affine, the bias is arbitrary, and all signed cancellations are allowed. Both signs of $b_h$ and constant denominators are included.

The same truth table has a representation with $d$ admissible original heads, zero bias, and relative full-cube amplitude margin at least

$$ \Gamma_n=\frac1{d^{d/2+3}(2n+1)^{2n+1}}. $$

In particular, $\log(1/\Gamma_n)=O(n\log n)$. At every original width $H\geq n+1$, this is a repair without any increase in width. The new denominators are the fixed dictionary $h+|x|$ for $1\leq h\leq n+1$; they do not depend on the target.

This is a written theorem. The exact scalar Cauchy interpolation and genuine positive-affine-ratio constructor are already Lean checked in `Atoms/ExactHammingProfile.lean`, `Atoms/PartialFraction.lean`, and `Atoms/PositiveAffineRatio.lean`. The coefficient bounds and complete quantitative repair below are not yet formalized. The original unrestricted denominator-direction hypothesis is not removed.

## Integer separators on the Hamming slices

On the slice $|x|=k$, the original score is affine in $x$:

$$ S(x)=\left(b+\sum_h\frac{a_{h,0}}{a_h+b_hk}\right)+\sum_i\left(\sum_h\frac{a_{h,i}}{a_h+b_hk}\right)x_i. $$

Thus its strict labels on that slice admit an affine separator. The integer-separator argument from [the one-head repair](margin_repair_one_head_positive.md) applies separately to each finite slice. If its feature rows do not span all $d$ dimensions, first choose independent columns spanning the feature-matrix column space. Every score vector is then still represented by this column basis, and the active-constraint argument applies in its rank $r\leq d$. Restore zero coefficients in omitted columns afterward.

The resulting integer affine numerators

$$ A_k(x)=a_{k,0}+\sum_{i=1}^n a_{k,i}x_i $$

satisfy

$$ F(x)A_k(x)\geq1\quad\text{when }|x|=k,\qquad |a_{k,i}|\leq d^{d/2}. $$

The coefficient estimate follows from $r^{r/2}\leq d^{d/2}$. This separate slice construction is essential: it prevents an unnecessary determinant bound in dimension $d^2$.

## An explicit bounded Cauchy inverse

Fix one coefficient position $i\in\lbrace0,\ldots,n\rbrace$ and put $w_k=a_{k,i}$. Define

$$ Q(t)=\prod_{h=1}^{d}(t+h),\qquad P_i(t)=\sum_{k=0}^n w_kQ(k)\prod_{\substack{0\leq j\leq n\cr j\neq k}}\frac{t-j}{k-j}. $$

The polynomial $P_i$ has degree at most $n=d-1$ and satisfies $P_i(k)=w_kQ(k)$. Its partial fractions are

$$ \frac{P_i(t)}{Q(t)}=\sum_{h=1}^{d}\frac{c_{h,i}}{t+h},\qquad c_{h,i}=\frac{P_i(-h)}{\prod_{\substack{1\leq\ell\leq d\cr\ell\neq h}}(\ell-h)}. $$

Every denominator in the coefficient formula is a nonzero integer, so its absolute value is at least one. For $0\leq k\leq n$ and $1\leq h\leq d$, the elementary estimates

$$ Q(k)\leq(2n+1)^d,\qquad \left|\prod_{\substack{0\leq j\leq n\cr j\neq k}}\frac{-h-j}{k-j}\right|\leq(2n+1)^n $$

hold: each numerator factor is at most $2n+1$ in absolute value and each nonzero integer denominator factor is at least one. Consequently

$$ |c_{h,i}|\leq d^{d/2+1}(2n+1)^{2n+1}. $$

Evaluating the partial fractions at the integer node $k$ gives the exact inverse relation

$$ \sum_{h=1}^{d}\frac{c_{h,i}}{k+h}=a_{k,i}. $$

## Assemble the admissible repair and bound its margin

For each $h\in\lbrace1,\ldots,d\rbrace$, use the genuine head

$$ \phi_h(x)=\frac{c_{h,0}+\sum_i c_{h,i}x_i}{h+|x|}. $$

Its denominator has a positive constant term and all slopes equal to one, so `FracAtom.ofPositiveAffineRatio` applies. Summing the preceding inverse relation over numerator positions gives

$$ \sum_{h=1}^{d}\phi_h(x)=A_{|x|}(x). $$

Therefore every signed score is at least one on the whole cube. Each head's full-cube norm is at most $d^{d/2+2}(2n+1)^{2n+1}$, because its denominator is at least one and its numerator has at most $d$ terms. The total head-amplitude norm is at most $d^{d/2+3}(2n+1)^{2n+1}$. Dividing proves the stated margin.

## What this positive theorem isolates

Arbitrary poles, either orientation, unrestricted numerators, and signed cancellation do not obstruct repair when all denominators share this direction. Hamming weight has only $n+1$ levels, and each level leaves an affine threshold problem. This supplies a controlled finite interpolation problem.

The binary-address direction in the [shared-direction obstruction](margin_repair_shared_direction_obstruction.md) instead has $2^n$ distinct levels. There, even arbitrary same-direction poles and arbitrary width cannot provide the desired margins for some targets. Thus the number of distinct statistic levels, rather than the existence of a common direction alone, is decisive for these two theorems. A general repair must either exploit few levels or change denominator directions in a more substantial way.

The root agent independently audited the integer separator on each slice, the exact partial fractions, coefficient estimates, original admissibility, and full-cube amplitude bounds before this checkpoint. The quantitative Hamming-direction repair remains a written theorem; the separate one-head integer-separator bridge is now kernel checked as recorded in the [one-head repair note](margin_repair_one_head_positive.md).
