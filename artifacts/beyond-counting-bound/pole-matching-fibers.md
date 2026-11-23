# Factorially Many Positive Interpolation Branches

## Scope

This construction concerns an auxiliary root-counting mechanism. It does not prove the requested lower bound on $W(n)$. The interpolation map below is a coordinate restriction of the manuscript's parameter space, with some numerator and denominator coefficients fixed. No bound for unrestricted square evaluation fibers is asserted.

## Theorem

Let $H\geq2$, $k\geq2$, and $d=\lceil\log_2(2H)\rceil$. Put $n=d+k$. There is a family of admissible $H$-head scores with $2Hk$ free real parameters, and a set of $2Hk$ cube vertices, such that their evaluation map has at least

$$ (H!)^{k-1} $$

regular preimages of the same data. All these preimages have positive integer denominator slopes. They define pairwise different real functions on the full cube and are pairwise inequivalent under global head permutations. A nonempty open set of interpolation data has at least this many distinct positive representations in this parameter family.

## The parameter family

Write the inputs as $(y,z)\in\lbrace0,1\rbrace^d\times\lbrace0,1\rbrace^k$ and define

$$ T(y)=1+\sum_{a=1}^d2^{a-1}y_a,\qquad S_{u,b}(y,z)=\sum_{h=1}^H\frac{\sum_{j=1}^k u_{hj}z_j}{T(y)+\sum_{j=1}^k b_{hj}z_j}. $$

The parameters $u_{hj}\in\mathbb R$ and $b_{hj}\gt0$ are free. All address coefficients in the numerator are fixed to zero, and those in the denominator are fixed to $2^{a-1}$. Thus the construction retains the original architecture and imposes an affine coordinate restriction on its parameters.

For $1\leq t\leq2H$, let $y(t)$ be the binary encoding of $t-1$. The sampled inputs are $(y(t),e_j)$, for $1\leq j\leq k$. There are exactly $2Hk$ distinct inputs.

## Integer slopes with distinguishable matchings

Choose distinct primes $p_{jrs}\gt3$, indexed by $2\leq j\leq k$ and $1\leq r,s\leq H$. Choose positive integers $b_{hj}$ satisfying the following congruences modulo each $p^2=p_{jrs}^2$:

$$ b_{r1}\equiv0,\qquad b_{h1}\equiv1\quad(h\neq r),\qquad b_{sj}\equiv p-1,\qquad b_{hj}\equiv1\quad(h\neq s). $$

At this modulus, set the residues of entries in other selector columns to one. These prescriptions are consistent because distinct triples use distinct prime moduli. The Chinese remainder theorem supplies each entry independently; adding a common positive multiple of the product of the moduli makes every entry positive.

For fixed $j,r,s$, the integer $1+b_{r1}+b_{sj}$ is divisible by $p_{jrs}$ exactly once. None of the other integers $1+b_{a1}+b_{cj}$ is divisible by this prime: their residues are $2$, $1$, or $3$. In particular, the entries within each selector column are distinct.

Choose permutations $\pi_1,\ldots,\pi_k$ of $\lbrace1,\ldots,H\rbrace$, with $\pi_1$ the identity. Define the parameter point

$$ u_{hj}^{\pi}=1,\qquad b_{hj}^{\pi}=b_{\pi_j(h),j}. $$

There are $(H!)^{k-1}$ such points. On the sampled inputs their scores are independent of all the permutations:

$$ S_{u^{\pi},b^{\pi}}(y(t),e_j)=\sum_{h=1}^H\frac1{t+b_{hj}}. $$

They nevertheless give different full-cube functions. Suppose $\pi_j(r)=s$ but $\tau_j(r)\neq s$. At the input $(0,e_1+e_j)$ their scores are

$$ 2\sum_{h=1}^H\frac1{1+b_{h1}+b_{\pi_j(h),j}},\qquad 2\sum_{h=1}^H\frac1{1+b_{h1}+b_{\tau_j(h),j}}. $$

The first sum has exactly one summand whose reduced denominator is divisible by $p_{jrs}$, and that denominator has valuation one. The second sum has no such summand. The two rational numbers cannot be equal. Explicitly, cancel common summands and multiply their difference by the product of its denominators. Modulo $p_{jrs}$, exactly one term survives, and it is nonzero because $p_{jrs}\gt3$. This proves distinctness without any assertion about generic real numbers.

Global head permutations preserve the full score function, so the distinct functions also prove inequivalence under that symmetry.

## Regularity

The Jacobian of the sampled evaluation map is block diagonal across selector coordinates. Up to a permutation of its columns, each block has columns

$$ \left(\frac1{t+b_h}\right)_{t=1}^{2H},\qquad \left(-\frac1{(t+b_h)^2}\right)_{t=1}^{2H},\qquad 1\leq h\leq H. $$

Here the $b_h$ are distinct positive numbers. These $2H$ columns are independent. Indeed, suppose

$$ R(t)=\sum_{h=1}^H\left(\frac{a_h}{t+b_h}+\frac{c_h}{(t+b_h)^2}\right) $$

vanishes at $1,\ldots,2H$. Multiplying by $Q(t)=\prod_h(t+b_h)^2$ gives a polynomial of degree at most $2H-1$ with $2H$ distinct roots. It is identically zero. Evaluation at $t=-b_h$ gives $c_h=0$, since all remaining factors are nonzero. After these coefficients vanish, the ordinary partial-fraction identity, or division by $t+b_h$ followed by evaluation there, gives $a_h=0$. Thus every Jacobian block is invertible.

The inverse function theorem applies at each of the finitely many parameter points. Intersect their open image neighborhoods. Shrink their parameter neighborhoods to keep every denominator slope positive and to retain the finitely many strict inequalities between the distinguishing full-cube evaluations. The intersection is a nonempty open set of data with the claimed number of distinct positive representations. $\blacksquare$

## Quantitative obstruction and limitation

No fixed constant $C$ can bound the number of these restricted positive interpolation branches by $C^{nH}H!$. This failure occurs even when $H$ is of order $2^n/n^2$.

To see this, take $H=2^{d-1}$ and $k=\lceil2\log_2 d\rceil$, so $n=d+k$. Then

$$ \frac{Hn^2}{2^n}=\frac{n^2}{2^{k+1}}=\Theta(1). $$

For the ratio of the claimed branch count to the proposed upper bound, elementary factorial estimates give

$$ \log\frac{(H!)^{k-1}}{C^{nH}H!}=(k-2)\log(H!)-nH\log C\geq\frac{(k-2)H}{2}\log(H/2)-nH\log C\to+\infty. $$

The leading positive term has order $Hn\log n$, whereas the subtracted term has order $Hn$. Thus positivity and quotienting by global head permutations do not justify this uniform branch estimate for parameter slices.

This does not settle sign counting. All the constructed scores are nonnegative, and are strictly positive whenever $z\neq0$. The different real-valued branches therefore have the same Boolean sign pattern. Counting them can substantially overcount Boolean functions. A method that counts sign patterns without counting these interpolation branches is not contradicted by this construction. Also, the logarithm of the branch count at the critical scale is only of order $2^n\log n/n$, which is smaller than $2^n$.

No statement about $W(n)$ follows without another mechanism. The original target remains unchanged and unproved.

## Small integer alternative and kernel audit

The prime construction above can be replaced by small integer slopes, at the cost of allowing the distinguishing address to depend on the two matchings. Index the heads by $h=0,\ldots,H-1$, fix the first selector column, and set

$$ b_{h1}=h+1,\qquad b_{hj}^{\pi}=H(\pi_j(h)+1)\quad(2\leq j\leq k). $$

All slopes lie between one and $H^2$. Each column still has distinct entries, so the same Jacobian proof establishes regularity at every matching. All one-selector values agree, exactly as before. It remains to prove that two different matchings give different full-cube functions.

On a two-selector slice, the score is twice the reciprocal sum with poles

$$ p_h=H+2+h+H\pi_j(h),\qquad S(y,e_1+e_j)=2\sum_h\frac1{t(y)+p_h},\qquad t(y)=\sum_{a=1}^d2^{a-1}y_a. $$

The two digits $h$ and $\pi_j(h)$ are recovered from $h+H\pi_j(h)$ by remainder and quotient upon division by $H$. Thus different matchings yield different pole sets.

**Finite-sample separation.** Let $p_1,\ldots,p_H$ be distinct real numbers and let $q_1,\ldots,q_H$ be another list. If the two reciprocal sums agree at $2H$ distinct points where every denominator is nonzero, then every $p_i$ occurs in the second list.

**Proof.** Set $Q_p(X)=\prod_i(X+p_i)$ and define $Q_q$ similarly. Clearing denominators gives the comparison polynomial

$$ P(X)=\left(\sum_i\prod_{r\neq i}(X+p_r)\right)Q_q(X)-\left(\sum_i\prod_{r\neq i}(X+q_r)\right)Q_p(X). $$

Its degree is at most $2H-1$. Agreement at $2H$ distinct regular samples forces $P=0$. Evaluation at $X=-p_i$ then gives

$$ 0=\prod_{r\neq i}(p_r-p_i)\prod_r(q_r-p_i). $$

The first product is nonzero by distinctness, so one factor in the second vanishes. This proves the claim. $\blacksquare$

Apply it at the integer samples $0,\ldots,2H-1$, all supplied by the $d$ address bits. Different pole sets must differ at one of these samples. This proves the full-cube distinctness needed in the original regular-branch theorem, with the small slopes displayed above.

`formalization/HeadComplexity/Atoms/PermutationPoleFibers.lean` proves the finite-sample separation, injective two-digit encoding, detection of distinct matchings, invariance of zero- and one-selector slices, and an injective family of $(H!)^{k-1}$ sampled tables. The formal sampled-table numerator is constant one in each head. On a slice with $r$ active selectors, the numerator in the original regular-fiber construction multiplies that table by $r$, so the zero-, one-, and two-selector identities transfer directly. The binary-address encoding, the regular Jacobian argument, and the inverse-function conclusion remain written proofs. No unrestricted parameter-fiber component count is claimed.

The independent exact verifier checks the matching tables and literal atom realizations on small full cubes. All six printed Lean declarations use only standard foundational axioms. This refinement does not change the quantitative limitation or the main target.
