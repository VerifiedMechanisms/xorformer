# Margin repair for affine factor products

## A positive two-head repair

Every product of two linear threshold truth tables has an original two-head representation with relative margin at least

$$ \gamma_2(n)=\frac{1}{12(n+1)^4((n+1)!)^2}. $$

Here product means agreement of the two Boolean labels, equivalently product of their signed labels. Neither affine factor is required to have coherent slope signs.

This is kernel checked as `HeadComplexity.TwoFactorMarginRepair.hasRelativeMargin_of_two_LTFs` in `formalization/HeadComplexity/Research/TwoFactorMarginRepair.lean`. The declaration `computableWithHeadsN_of_two_LTFs` explicitly returns a representation in the unchanged original model. The bounded-coefficient version is `hasRelativeMargin_of_bounded_affine_product`. The norms are exactly the individual full-cube head norms in `RelativeMarginQuantifiers`.

The result repairs the truth table of a simple two-head collision jet. It does not assert repair of every unrestricted two-head score, nor does it permit replacing one summand by a merely sign-equivalent summand inside a larger cancelling sum.

## Construction

Apply `IntegerSeparatorMarginRepair.exists_bounded_integer_affine` separately to the two threshold factors. This gives affine forms $A,D$ with integer coefficients bounded in absolute value by $M=(n+1)!$, with the correct signs and absolute values at least one on the entire cube. Put $d=n+1$, $U=dM$, and

$$ B(x)=1+\sum_i x_i,\qquad \varepsilon=\frac1{2U},\qquad S(x)=\frac{A(x)}{B(x)}-\frac{A(x)}{B(x)+\varepsilon D(x)}. $$

Every coefficient of the perturbed denominator is positive, because $\varepsilon M\leq1/2$. Its values lie between $1/2$ and $2d$. Both displayed ratios are therefore genuine original heads, with unrestricted affine numerators. The exact identity

$$ S(x)=\frac{\varepsilon A(x)D(x)}{B(x)(B(x)+\varepsilon D(x))} $$

preserves the product sign. Its signed score is at least $\varepsilon/(2d^2)$. The two full-cube norms are at most $U$ and $2U$, so their sum is at most $3U$. Dividing gives $1/(12d^4M^2)$.

This construction changes the denominator directions. It applies even when the original collision score used arbitrarily small separation between two bounded-condition denominators. Integer refitting of the factors removes that irrelevant separation scale.

## General mixed finite differences

The following extension is a written proof. It is not claimed as a Lean declaration.

Suppose a truth table is the sign of a product of $k\geq1$ nonvanishing real affine forms. Refit the sign of each factor independently to obtain integer affine forms $A_1,\ldots,A_k$, each with coefficient bound $M=(n+1)!$ and full-cube absolute value at least one. Put $d=n+1$, $q=k-1$, $B(x)=1+\sum_i x_i$, and $\varepsilon=1/(2kdM)$. Define

$$ S(x)=A_1(x)\sum_{T\subseteq\lbrace2,\ldots,k\rbrace}\frac{(-1)^{|T|}}{B(x)+\varepsilon\sum_{i\in T}A_i(x)}. $$

This uses $2^{k-1}$ heads. Every denominator coefficient is at least $1-\varepsilon kM\geq1/2$, and every denominator value on the cube is between $1/2$ and $2d$. Thus all heads are admissible, including when individual factor coefficients have arbitrary signs.

Repeated use of the fundamental theorem of calculus gives the mixed finite-difference identity

$$ \sum_{T\subseteq\lbrace2,\ldots,k\rbrace}\frac{(-1)^{|T|}}{B+\varepsilon\sum_{i\in T}A_i}=\varepsilon^q q!\left(\prod_{i=2}^k A_i\right)\int_{[0,1]^q}\left(B+\varepsilon\sum_{i=2}^k t_iA_i\right)^{-q-1}dt. $$

In this display the integral is ordinary integration over the unit cube. All intermediate denominators remain positive because they are convex combinations of the subset denominators. The identity is valid for either sign of every $A_i$. The two sign factors from the mixed difference and the derivative of the reciprocal cancel. For $q=0$, the integral notation denotes the single value $B^{-1}$.

There is also an entirely algebraic identity. For increments $a_1,\ldots,a_q$, let $s_{\pi,j}=\sum_{i=1}^j a_{\pi(i)}$ and $s_{\pi,0}=0$. Whenever all subset denominators are nonzero,

$$ \sum_{T\subseteq\lbrace1,\ldots,q\rbrace}\frac{(-1)^{|T|}}{B+\sum_{i\in T}a_i}=\left(\prod_{i=1}^q a_i\right)\sum_{\pi\in\mathfrak S_q}\prod_{j=0}^q\frac1{B+s_{\pi,j}}. $$

To prove this, induct on $q$. Subtract the formula with base $B+a$ from the formula with base $B$. For each old permutation, telescope the difference of its two products of reciprocal factors. Each telescoping summand supplies a factor $a$ and inserts one additional partial-sum denominator. Its position is exactly the position where $a$ is inserted into the permutation. The $q+1$ insertion positions and all old permutations enumerate the new permutations once. This proves the identity for arbitrary signed increments, including zero increments. When the subset denominators are positive and at most $2d$, the permutation formula directly gives the same lower bound as the integral formula.

The score has the desired product sign and signed magnitude at least $\varepsilon^q q!/(2d)^{q+1}$. Every head norm is at most $2dM$, giving the relative-margin bound

$$ \gamma_k(n)\geq\frac{(k-1)!}{4^k(2k)^{k-1}d^{2k}M^k}. $$

For $1\leq k\leq n$, the negative logarithm of this bound is $O(n^2\log(n+1))$. It is therefore much smaller than either $\exp(\sqrt n)$ or $\exp(n/\log n)$ for sufficiently large $n$. These product truth tables meet both requested margin thresholds at the same $2^{k-1}$ width as their mixed-difference construction.

## The remaining cancellation problem

The finite-difference formula is a positive repair theorem for an explicitly identified class of multivariate collision limits. It does not show that an arbitrary cluster has a leading table which factors into affine signs. A general leading jet can be a sum of such products, and changing the magnitude of an individual product can change the sign of that sum.

For example, even the elementary replacement of a positive factor by another positive factor need not preserve a score after adding a negative bias. The original target must be preserved by the whole repair. The next missing statement would control a jointly refitted sum of collision jets, with a total head budget and full-cube norm bound that depend on the source width rather than the number of monomials after expansion. No such statement is proved here.
