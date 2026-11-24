# Head capacity with ordinary Cayley–Bacharach pole support

## What is proved

This note combines the written geometric theorems in `cayley_bacharach_base_locus.md` and `weighted_incidence_capacity.md` with the kernel-checked active-coefficient certificate in `Research/PartialLinearCapacity.lean`. The resulting theorem is a written proof, not a Lean declaration.

For $N=2^n$ and every sufficiently large $n$, at most $2^{N/2}$ Boolean truth tables have an $H$-head original-model representation whose normalized, distinct pole points satisfy the following ordinary Cayley–Bacharach condition, at either of these scales:

$$ H=\left\lfloor\frac{N}{100n^{3/2}}\right\rfloor,\qquad D_0=\lfloor\exp(\sqrt n)\rfloor; $$

or

$$ H=\left\lfloor\frac{N\log n}{100n^2}\right\rfloor,\qquad D_0=\lfloor\exp(n/\log n)\rfloor. $$

The condition is $\mathrm{CB}(D_0)$ for the normalized denominator points in affine coefficient space: every polynomial of degree at most $D_0$ vanishing at all but one of these points also vanishes at the last. All numerator coefficients, the bias, and signed cancellations remain arbitrary. There is no relative-margin hypothesis.

This is a restricted count. It does not assert that every low-margin truth table admits such a representation, and does not imply either requested unrestricted lower bound for `HeadComplexity.worstCaseHeadComplexity`.

## Normalized original heads and linear coefficients

Every original `FracAtom` denominator is positive on the full Boolean cube and has positive constant coefficient. Divide its numerator and denominator by that constant. The score has the form

$$ S(x)=a_\varnothing+\sum_{h=1}^H\frac{a_{h,0}+\sum_{i=1}^n a_{h,i}x_i}{1+b_h\cdot x}. $$

This formula is an enlargement of the original admissible class when arbitrary normalized pole points with positive Boolean denominators are allowed. Counting the enlarged class is therefore sufficient. No change to the original definition is made. The normalization and affine ratio identities are already checked in `Research/OriginalMarginCapacity.lean` as `denominatorCoefficients_constant_pos` and `affineRatio_eq_eval`.

Set $\ell=1+(n+1)H$. Clear the positive common denominator $\prod_h(1+b_h\cdot x)$. For each Boolean input the resulting polynomial is linear in these $\ell$ score coefficients, with feature entries of total degree at most $H$ in the pole parameters. Full-cube signs are unchanged because the multiplier is positive.

The existing active-coefficient certificate says that every strict table occurs in one of

$$ C_{n,H}=2^\ell\binom{N+2\ell}{\ell} $$

polynomial charts. Each chart uses only the pole parameters and one real box-radius parameter $T$. Its score polynomials have total degree at most $2H\ell+1$. This follows from the kernel-checked declarations `exists_unsigned_basis`, `eval_reconstructedScore_eq`, `card_certificate`, and `certificateScore_totalDegree_le` in namespace `HeadComplexity.PartialLinearCapacity`; the wrapper `exists_certificate_pattern` packages the same construction. In particular, the construction preserves the chosen pole parameters. The box is chosen after the real coefficient vector, so this imposes no a priori coefficient bound.

## Exact finite bound

Fix integers $D_0\geq s\geq1$, and suppose the $H$ distinct pole points satisfy $\mathrm{CB}(D_0)$. Put

$$ m=\left\lfloor\frac{D_0+2}{s+1}\right\rfloor,\qquad M_\ast=\lfloor H/m\rfloor,\qquad R=\binom{n+s}{n},\qquad r_\ast=\max\lbrace r\leq n:\binom{s+r}{r}\leq H\rbrace. $$

The preceding Hilbert-function argument gives a determining subset of size $M=h_\Gamma(s)\leq M_\ast$. Its indices have at most $\binom HM$ choices. There are at most $\binom RM$ choices for an invertible monomial-column minor of its evaluation matrix.

On a fixed such chart, the condition that another pole belongs to the same degree $s$ base locus is given by the augmented minors using these fixed columns. Their degree is at most $sM$ in the determining coordinates and at most $s$ in the other pole. At an invertible determining minor, the complex fiber for each additional pole has dimension at most $r_\ast$: the degree $s$ Hilbert function of that base locus is at most $M\leq H$.

Give the $nM$ determining coordinates weight one and all other pole coordinates, together with $T$, weight $M$. Define

$$ K=nH+1,\qquad q_M=n(H-M)+1,\qquad c_M=(n-r_\ast)(H-M),\qquad d_M=nM+r_\ast(H-M)+1. $$

Thus $c_M+d_M=K$. The incidence equations have weighted degree at most $L=2sM$. The extra variable $T$ is unrestricted in the fiber. Set

$$ E=\max\lbrace 2H\ell+1,4s\rbrace. $$

Every certificate score has weighted degree at most $D=ME$, and $D\geq2L$. The weighted incidence theorem applies to the subset where the determining minor is invertible. It does not require control of the rank-drop locus elsewhere.

Consequently the number of strict tables in this pole-restricted class is at most

$$ C_{n,H}6^K\sum_{M=1}^{M_\ast}\binom HM\binom RM M^{nM}(4s)^{c_M}E^{d_M}\sum_{j=0}^{d_M}\binom{2N+1}{j}. $$

If $M_\ast=0$, the class is empty. If $M=H$ or $r_\ast=n$, then $c_M=0$ and the unconstrained case of the weighted incidence theorem applies. This finite bound charges every discrete chart and every active coefficient certificate.

## Square-root scale

Take $D_0=\lfloor\exp(\sqrt n)\rfloor$ and $s=\lfloor D_0/n^3\rfloor$. For sufficiently large $n$, $s\geq1$, $s+1\leq2D_0/n^3$, and the block Hilbert estimate gives

$$ M_\ast\leq4H/n^3. $$

Since $r_\ast\leq n$, the inequality $\binom{s+r_\ast}{r_\ast}\geq(s/n)^{r_\ast}$ gives

$$ r_\ast\leq2(\log2)\sqrt n\qquad(H\leq2^n). $$

For $H=\lfloor cN/n^{3/2}\rfloor$, with fixed $c\gt0$, the logarithms of the two principal degree factors satisfy, uniformly in $1\leq M\leq M_\ast$,

$$ c_M\log(4s)\leq n^{3/2}H+O(nH), $$

and

$$ d_M\log E\leq4(\log2)^2n^{3/2}H+o(n^{3/2}H). $$

For the second estimate use $d_M\leq4H/n^2+2(\log2)\sqrt n H+1$ and $\log E\leq2n\log2+O(\log n)$.

All remaining factors contribute $o(n^{3/2}H)$. Here are bounds sufficient to justify that assertion. The certificate factor has logarithm $O(nH\log n)$. The factor $6^K$ costs $O(nH)$. The combined determining-index, monomial-minor, and $M^{nM}$ factors cost at most

$$ M\log H+M\log R+nM\log M=O(H/n)+O(H/n^{3/2}), $$

using $\log R\leq n\log(n+s)=O(n^{3/2})$. The sum over $M$ contributes at most $\log H=O(n)$. Finally $d_M=O(N/n)$ at this width, so the usual binomial sum bound gives

$$ \log\left(\sum_{j=0}^{d_M}\binom{2N+1}{j}\right)=O(\sqrt n H\log n)+O(n)=o(n^{3/2}H). $$

It follows that

$$ \log T\leq\left(1+4(\log2)^2+o(1)\right)cN. $$

Since $1+4(\log2)^2\lt3$ and $3/100\lt(\log2)/2$, taking $c=1/100$ proves $T\leq2^{N/2}$ for every sufficiently large $n$.

## Logarithmic scale

Take $D_0=\lfloor\exp(n/\log n)\rfloor$, $s=\lfloor D_0/n^3\rfloor$, and $H=\lfloor cN\log n/n^2\rfloor$. The same arguments give

$$ M_\ast\leq4H/n^3,\qquad r_\ast\leq2(\log2)\log n. $$

The leading incidence factor obeys

$$ c_M\log(4s)\leq\frac{n^2H}{\log n}+O(nH)=cN+o(N). $$

The score-degree factor costs $O(nH\log n)=O(N(\log n)^2/n)=o(N)$. The certificate, active-subset, determining-subset, monomial-minor, and summation terms also cost $o(N)$ by the same estimates, with $r_\ast=O(\log n)$. Hence

$$ \log T\leq(c+o(1))N. $$

Again $c=1/100$ gives $T\leq2^{N/2}$ for every sufficiently large $n$.

The same conclusions hold if the effective number of distinct pole points is any positive integer at most the displayed width and its support satisfies the same Cayley–Bacharach condition. Sum the finite bounds over those widths. The preceding estimates are uniform after bounding the large degree parameter by the maximum width; the extra logarithm is $O(n)=o(N)$. Repeated identical denominators can be merged by adding their affine numerators, which is legitimate in the enlarged rational class used for this upper count.

## First-order ordinary moments suffice

Let the distinct normalized pole points be $b_1,\ldots,b_H$. Suppose there are scalars $c_h$ and vectors $v_h$, with $(c_h,v_h)\neq(0,0)$ for each $h$, such that the ordinary polynomial functional

$$ \Lambda(P)=\sum_{h=1}^H\left(c_hP(b_h)+v_h\cdot\nabla P(b_h)\right) $$

annihilates every polynomial of total degree at most $2D_0+1$. Then the reduced support $\lbrace b_1,\ldots,b_H\rbrace$ satisfies $\mathrm{CB}(D_0)$, and the finite and asymptotic counts above apply without any additional parameter cost.

**Proof.** Suppose $F$ has degree at most $D_0$, vanishes at every pole other than $b_h$, and satisfies $F(b_h)\neq0$. At every other pole, both the value and all first derivatives of $F^2$ vanish. If $v_h=0$, then $c_h\neq0$ and

$$ \Lambda(F^2)=c_hF(b_h)^2\neq0, $$

contrary to the moment hypothesis. If $v_h\neq0$, choose an affine polynomial $\ell$ with $\ell(b_h)=0$ and $v_h\cdot\nabla\ell\neq0$. The product rule gives

$$ \Lambda(F^2\ell)=F(b_h)^2v_h\cdot\nabla\ell\neq0. $$

The degree is at most $2D_0+1$, again a contradiction. This proves reduced Cayley–Bacharach over the reals; a complex separator would have a real or imaginary part giving a real separator, so the complex condition used by the Hilbert-function theorem also follows. $\blacksquare$

The auxiliary moment functional need not equal the numerator coefficients in the represented score. The conclusion is a restriction on the pole support, after which all score numerators are counted freely. In particular, this proof does not turn cancellation of Boolean reciprocal evaluations into ordinary polynomial moment annihilation.

More generally, let a finite algebra at each distinct pole have maximal-ideal nilpotence index at most $q$, and let a polynomial functional have a nonzero restriction to every local factor. Ordinary annihilation through degree $qD_0+q-1$ again forces the reduced support to satisfy $\mathrm{CB}(D_0)$. For a proposed separator $F$, the element $F^q$ vanishes in every other local algebra and is a unit in the chosen one. Polynomials of degree at most $q-1$ in centered coordinates span that local algebra. Thus some such polynomial $G$ has $\Lambda(F^qG)\neq0$, contradicting the degree bound. This extension costs the factor $q$ in ordinary moment order; it supplies no uniform bound on $q$ for arbitrary moment schemes.

## The precise remaining access problem

A sufficient ordinary-moment hypothesis is an annihilating coefficient vector with every coefficient nonzero on the distinct pole support, annihilating all polynomials of degree at most $D_0$. The preceding section also permits arbitrary first-order local functionals if the annihilation order is $2D_0+1$. Original Boolean score cancellation does not imply either hypothesis: it tests reciprocal kernels at only the Boolean inputs, and exact projection ghosts can survive at separated poles.

The useful dichotomy would therefore have to show that every narrow truth table either has the previously proved quantitative relative margin, or has a comparable-width representation belonging to one of these ordinary-moment classes, or to another class with an equally small count. No such dichotomy has been proved. General nonreduced local moment schemes with unbounded nilpotence index still require an additional argument; the finite-scheme separator result alone does not provide the required small determining data.
