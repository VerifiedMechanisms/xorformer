# Working notes: the order of W(n)

Run: "Worst-Case Head Complexity at Order 2^n/n^2". These notes record the audit of the
paper's W(n) results, the reformulations used, and the evidence gathered. Notation: $N=2^n$,
$s_x=2f(x)-1$.

## 1. Normalized family (audit of Theorem 2.6 and the normalization in Theorem 3.5)

Every $H$-head score can be written, without loss of generality, as

$$ S(x)=\sigma+\sum_{h\in P}\frac{u_h\cdot x}{1+b_h\cdot x}+\sum_{h\in M}\frac{v_h\cdot(\mathbf 1-x)}{1+d_h\cdot(\mathbf 1-x)},\qquad b_h,d_h\in\mathbb R^n_{\geq0}. $$

Reason. Divide each atom by $B_h(0)>0$ (positive-slope heads) and write $A_h/B_h=A_h(0)+(u_h-A_h(0)b_h)\cdot x/B_h$;
the constants are absorbed into $\sigma$. A negative-slope head $A/(b_0+b\cdot x)$ with $b\leq0$ and
$b_0+\sum_i b_i\gt0$ equals, in the complemented variables $y=\mathbf 1-x$, an atom with denominator
$(b_0+\sum_ib_i)+\sum_i|b_i|y_i$, which has positive slopes. So M-heads are P-heads in complemented
coordinates. Constant-slope heads are affine functions and are absorbed (one extra head at most, or
into any P-head by the paper's perturbation argument).

## 2. Equivalent forms of the family

1. Tensor form: $S(x)=\sigma+x^{\top}Wr(x)$ with $r_h(x)=1/(1+b_h\cdot x)$ and $W\in\mathbb R^{n\times H}$.
   For fixed denominators the realizable $f$ are exactly the halfspace dichotomies of the $N$ points
   $(1,x\otimes r(x))\in\mathbb R^{1+nH}$ (this is the paper's Proposition 3.11 in other words).
2. Module form: $S=\sigma+\sum_i x_iG_i$ with $G_i\in V_R:=\operatorname{span}\lbrace r_1,\dots,r_H\rbrace$.
3. Polarization form: with $B_h=1+b_h\cdot x$ and $A_h=u_h\cdot x$,
   $\prod_hB_h\cdot S=\sigma\prod_hB_h+\sum_hA_h\prod_{g\neq h}B_g=\frac{d}{d\varepsilon}\Big|_{0}\prod_h(B_h+\varepsilon A_h)+\sigma\prod_hB_h$.
   Hence $H^{\ast}(f)\leq H$ iff $f=\operatorname{sign}\big(\prod_h(B_h+\varepsilon A_h)-\prod_hB_h\big)$ for all small $\varepsilon\gt0$
   (after absorbing $\sigma$ into the numerators): the family is the set of first-order differences of two
   products of $H$ admissible affine forms. Equivalently $S=\frac{d}{d\varepsilon}\log\prod_h(B_h+\varepsilon A_h)$.

## 3. Where the information must sit

Fix the denominators. The numerators form a linear family of dimension $nH+1$, so by the Cover count
at most $2\sum_{i\leq nH}\binom{N-1}{i}\leq 2(eN/(nH))^{nH}$ functions are realizable. With $H=cN/n^2$ this is
$2^{(N/n)\log_2(ecn)+O(1)}\ll2^N$. Consequently:

- no fixed denominator list can realize all functions with $H\lt N/(3.1n)$ heads (solve $(N/t)\log_2(et)=N$);
- in the regime $H\asymp N/n^2$ the numerators carry only $O(\log n)$ bits per real parameter, while the
  $nH$ denominator parameters must carry $\Theta(n)$ bits each. The target bound is therefore equivalent
  to the statement that the sign pattern depends on the denominators in a Warren-tight way.

## 4. Two sub-families that are provably NOT Warren-tight (linear collapse)

Univariate analogue: $t\in\lbrace0,\dots,N-1\rbrace$, atoms $a_h/(1+b_ht)$. The sum is $P(t)/Q(t)$ with
$\deg P\leq H$, so at most $H$ sign changes and at most $2\sum_{j\leq H}\binom{N-1}{j}$ patterns: linear in $H$.

Common direction: $b_h=t_h\beta$ for one fixed $\beta\gt0$ and $s=\beta\cdot x$. Then
$\prod_{g\neq h}(1+t_gs)$, $h=1..H$, span the polynomials of degree $\leq H-1$ in $s$ for every choice of
distinct $t_h$, so the cleared score lies in the fixed linear space
$\lbrace R_0(s)+\sum_ix_iR_i(s):\deg R_0\leq H,\ \deg R_i\leq H-1\rbrace$ of dimension $(n+1)H+1$.
Its sign patterns are at most $2(eN/((n+1)H))^{(n+1)H}$, again linear-like: such lists need $H\gtrsim N/(3n)$.

Conclusion: a proof of the target must use denominators whose directions $b_h$ are genuinely spread, so that
the spaces $V_R$ (and the products $\prod_{g\neq h}B_g$) move with the parameters.

## 5. Localization available under admissibility

An admissible denominator $B=sC+\sum_{i\in T}\lambda_ix_i$ with $C$ positive affine and $\lambda_i\gg s$ makes
$1/B$ of size $1/s$ on the subcube $\lbrace x_T=0\rbrace$ and $O(1/\lambda)$ elsewhere; with negative slopes the same
holds for $\lbrace x_T=1\rbrace$. Mixed subcubes $\lbrace x_T=0,x_{T'}=1\rbrace$ are not available: the form
$\sum_T\lambda_ix_i+\sum_{T'}\lambda_i(1-x_i)$ has mixed slopes. The paper's star cells $N(v)$ are zero sets of
$\operatorname{dist}(v,x)-1$, which also has mixed slopes; the paper circumvents this only for EXACT spanning,
by an algebraic continuation in the scale $s$ of a nonvanishing determinant (Lemma on affine zero-set
partitions). That continuation does not transfer to sign-only statements.

Any head that dominates on a cell forces an affine sign pattern there, so cells of a dominating head have
at most $n+1$ points: dominant-head constructions are capped at $N/(n+1)$ heads. A $2^n/n^2$ construction
must have $\Theta(n)$ heads contributing comparably at a typical point.

## 6. A rigorous linear-collapse theorem for common-direction lists

**Theorem (common direction).** Let $\beta\in\mathbb R^n_{\geq0}$ and suppose every denominator has the form
$B_h=1+t_h\,\beta\cdot x$ with $t_h\gt0$ (or every $B_h=1+t_h\beta\cdot(\mathbf 1-x)$). Then the set of Boolean
functions sign-represented by $\sigma+\sum_{h\leq H}A_h/B_h$ with affine $A_h$ is contained in the set of
sign patterns of the fixed linear space

$$ \mathcal W=\Big\lbrace R_0(s)+\sum_{i=1}^n x_iR_i(s):\ \deg R_0\leq H,\ \deg R_i\leq H-1\Big\rbrace,\qquad s=\beta\cdot x, $$

of dimension at most $(n+1)H+1$. Consequently at most $2\sum_{i\leq (n+1)H+1}\binom{N-1}{i}$ functions are
representable, and a representation of every (or of almost every) Boolean function by such a list needs
$H\geq(\tfrac12-o(1))N/(n+1)$.

**Proof.** Multiply the score by $Q(s)=\prod_h(1+t_hs)\gt0$. Then $Q\cdot S=\sigma Q(s)+\sum_i x_i\sum_h a_{h,i}\prod_{g\neq h}(1+t_gs)$
plus the constant parts of the numerators times $\prod_{g\ne h}(1+t_g s)$, which have degree $\leq H-1$ in $s$ and are absorbed
in $R_0$. Each inner sum is a polynomial in $s$ of degree $\leq H-1$ and $Q$ has degree $H$, so $Q\cdot S\in\mathcal W$.
Sign patterns of a linear space of dimension $D$ on $N$ points number at most $2\sum_{i\leq D}\binom{N-1}{i}$ (Cover).
This is $\lt2^N$ unless $D\geq(N-1)/2$, and it is $o(2^N)$ unless $D\geq N/2-O(\sqrt N)$. $\blacksquare$

The paper's spanning lists use $N/n$ distinct directions $\mathbf 1+v$, so this theorem does not touch them; it shows
that the degree-$H$ factor in Warren's bound is illusory unless the directions spread.

## 7. Literature synthesis (from the web survey, 20 Nov 2026)

- Rajaraman, Sundaram, Tesfaye, "The head complexity of Boolean functions in single-layer attention" (arXiv 2609.04046,
  Sep 2026): same scalar normal form (sum of $k$ ratios of affine functions), $k$ heads compute $k$-bit parity and not
  $(k+1)$-bit parity, universal bound $2^n$ heads, and the same Warren count $2^{O(kn^2)}$, hence $\Omega(2^n/n^2)$ for
  almost all functions. No upper bound below $2^n$ there; the paper audited here is ahead with $(1+o(1))2^n/n$.
- Hsu (arXiv 2605.12171) and Hsu, Xu (arXiv 2608.04243): parity lower bounds through Paturi, Saks (rational
  sign-representation of parity needs $\deg P+\deg Q\geq n$).
- O'Donnell, Servedio (CCC 2003): almost every function has threshold degree $\leq n/2+O(\sqrt{n\log n})$; the proof
  projects point indicators onto the low-degree space and needs codimension only $2^n/\mathrm{poly}(n)$ plus Hoeffding.
  Anthony (arXiv 2610.15057, Oct 2026): almost every function has threshold degree exactly $\lfloor n/2\rfloor$ or
  $\lceil n/2\rceil$ (Reed-Muller erasure recovery). These are statements about LINEAR families; they give at most
  constant-factor gains and do not transfer to the nonlinear denominator regime needed here.
- Baldi, Vershynin (2019): $\log_2T(n,d)=(1-o(1))\,n\binom{n}{\leq d}$ for $d=o(\log n)$; the hyperplane-arrangement
  count is tight for PTFs. This is the model case where a Warren-type count IS tight, but again for a linear family.

## 8. Rate caps for local mechanisms (audit of why the paper stops at $N/n$)

Let a set of $k$ heads dominate a cell $R$ (their denominators are $O(s)$ on $R$ and bounded below off $R$; all
other heads are bounded on $R$). Then the sign pattern on $R$ is a $k$-head pattern of the restricted problem,
so at most $2(e|R|/(2nk))^{2nk}$ patterns. All $2^{|R|}$ patterns are available only if $|R|\leq 2nk\log_2(e|R|/(2nk))$,
i.e. $|R|/k\approx 2n\log_2(|R|/(2nk))$ points per head. Reaching $n^2/c$ points per head forces $|R|\geq 2nk\,2^{n/(2c)}$:
cells must be exponentially large, so a $2^n/n^2$ construction cannot be assembled from cells of polynomial size.
For $k=1$ this is the paper's star cells ($n+1$ points per head); the inverse-function-theorem route is capped at
$2n$ points per head (parameter count), i.e. $W(n)\leq(\tfrac12+o(1))N/n$ at best; the paper achieves $2/3$.

## 9. The tropical (dominance) sub-model and its transfer theorem

Let head $h$ carry a permutation $\pi_h$ of $[n]$, integers $w_{h,1},\dots,w_{h,n}$ (all $nH$ integers distinct) and signs
$c_{h,k}\in\lbrace\pm1\rbrace$. For $x\neq0$ let $k_h(x)$ be the $\pi_h$-position of the first element of $\operatorname{supp}(x)$
in the order $\pi_h$. Define $T(x)=c_{h^{\ast},k_{h^{\ast}}(x)}$ where $h^{\ast}=\arg\max_h w_{h,k_h(x)}$.

**Theorem (tropical transfer).** If $T=2f-1$ on $\lbrace0,1\rbrace^n\setminus\lbrace0\rbrace$ then $H^{\ast}(f)\leq H$.

**Proof.** Put $L=2\max|w|+2$, $m_{h,\pi_h(k)}=kL$, $e_{h,\pi_h(k)}=kL+w_{h,k}$, $b_{h,i}=K^{m_{h,i}}$ and $u_{h,i}=c_{h,\pi_h^{-1}(i)}K^{e_{h,i}}$
for a large $K$. With $t=\pi_h(k_h(x))$, the numerator $u_h\cdot x$ equals $c_{h,k}K^{e_{h,t}}(1+O(nK^{-L/2}))$ and the denominator
$1+b_h\cdot x$ equals $K^{m_{h,t}}(1+O(nK^{-L/2}))$, because every other element of the support sits later in $\pi_h$ and has exponent at least
$L/2$ smaller. Hence $u_h\cdot x/(1+b_h\cdot x)=c_{h,k}K^{w_{h,k}}(1+O(nK^{-L/2}))$. Since the $nH$ weights are distinct integers the
head with the largest weight dominates the sum by a factor $K/(nH)$, so for $K\gt 4nH$ the sign of $\sigma+\sum_h u_h\cdot x/(1+b_h\cdot x)$
is $T(x)$ for $x\neq0$; choose $\sigma=2f(0)-1$. All slopes $b_{h,i}$ are positive, so Theorem 2.6 applies. $\blacksquare$

Equivalently $T$ is a decision list whose rules are the $nH$ subcubes $\Sigma_{h,k}=\lbrace x_{\pi_h(k)}=1,\ x_{\pi_h(j)}=0\ (j\lt k)\rbrace$
(one forced one, nested forced zeros), ordered by the weights, each rule carrying a sign. Negative-slope heads give the complementary rules
(one forced zero, nested forced ones). Counting: there are at most $(n!)^H(nH)!\,2^{nH}\leq2^{nH(n+1)}$ such lists, so the tropical model
cannot beat $H=(1-o(1))N/n^2$; it is a candidate for a Warren-tight mechanism, and it is a strict sub-model: parity needs about $N$ rules
in it (every fiber is a subcube minus earlier subcubes and must be an independent set of the cube graph), while $H^{\ast}(\mathrm{PARITY}_n)=n$.

## 10. Literature update (second survey)

- Depth-two threshold circuits (LTF of LTFs): Kane, Williams (2016) give the counting bound $\Omega(2^n/n^2)$ for almost all functions;
  the best known universal upper bound is the trivial $2^{n-1}+1$. So the exact analogue of our gap is open there with an even larger gap.
  Lupanov (1972) and Nechiporuk (1964): unbounded-depth threshold circuits have Shannon function $\sim2\sqrt{2^n/n}$.
- Selezneva: XOR sums of products of affine forms over $\mathbb F_2$ (indicators of affine subspaces) have Shannon function $\Theta(2^n/n^2)$:
  a Warren-tight dictionary result on the cube, over $\mathbb F_2$ and with exact XOR rather than real signs. Kirichenko (2005): XOR of
  products of literals needs at most $2^{n+1}(\log_2n+1)/n$ terms; Even, Kohavi, Paz lower bound $2^n/(n\log_23)$.
- Warren tightness: Basu, Pollack, Roy (2009) show products of $d$ generic linear forms attain $((2d)^m/m!)N^m$ connected sign cells;
  so Warren's bound is tight in the base constant for generic products of linear forms, but univariate sums of $t$ simple fractions have
  at most $t-1$ zeros (Laguerre, Descartes), and fewnomial (Khovanskii, Zell) bounds depend on the number of monomials, not the degree.
- Alon, Frankl, Rodl: sign rank of almost all $N\times N$ matrices is in $[N/32,N/2+o(N)]$; the Warren count is tight up to constants.
