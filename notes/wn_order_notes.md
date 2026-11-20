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
$2^{(cN/n)\log_2(en/c)+O(1)}\ll2^N$. Consequently:

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
$B_h=1+t_h\beta\cdot x$ with $t_h\gt0$ (or every $B_h=1+t_h\beta\cdot(\mathbf 1-x)$). Then the set of Boolean
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

## 11. The crux as an interpolation-multiplicity question

For fixed numerators and denominators the sign vector of $S(\cdot;\theta)$ is the cell of $\theta\in\mathbb R^{2nH}$ in the
arrangement of the $N$ hypersurfaces $W_x=\lbrace\theta:S(x;\theta)=0\rbrace$. Warren's proof bounds the number of cells by
$\sum_{k\leq2nH}\binom Nk I_k$ where $I_k$ bounds the number of connected components of $k$-fold intersections. For hyperplanes
$I_k=1$ and the count is linear-like; Warren uses the Milnor-Thom bound $I_k\leq(2\deg)^{2nH}$. Here a $k$-fold intersection with
$k=2nH$ is the set of parameter vectors whose score vanishes at $2nH$ prescribed cube points: the solution set of a rational
interpolation problem. So

- $W(n)=\Theta(N/n^2)$ is equivalent (up to constants in the exponent) to: generic interpolation problems "$S(x_j;\theta)=0$,
  $j\leq2nH$" have $2^{\Theta(nH\cdot n)}$ isolated real solutions, i.e. Bezout-like multiplicity;
- $W(n)=\Omega(N/n)$ would follow from: such problems have $2^{O(nH\log n)}$ real solutions (polynomially many per parameter).

In the univariate analogue the interpolation problem is linear after clearing denominators (Cauchy interpolation), so it has a
unique solution and the count is linear-like. For $H=1$ on the cube the problem is linear in $(u,b)$ (unique solution). For
$H\geq2$ the elimination of the numerators leaves $nH$ polynomial conditions of degree up to $H(nH+1)$ in the $nH$ denominator
parameters, whose Bezout number matches Warren; the actual number of real solutions in the admissible orthant is unknown. This
is the precise algebraic statement separating the two conjectures.

## 12. Experimental record (heuristic searches, not evidence of optimality)

- search2.py (alternating max-margin LP in the numerators, Danskin subgradient ascent on the denominators, multiplicative updates,
  random restarts, exact rational verification): random 7-bit functions found with 8 heads (none with 7); random 8-bit functions
  found with 12-14 heads (none with 10). Fixed generic lists succeed only when $nH\gtrsim N/2$ (Cover), so the optimizer does find
  genuinely nonlinear representations, but only slightly below $N/(2n)$: at $n=8$, $N/(2n)=16$, found $12$-$14$; $N/n^2=4$.
  The found denominators have dynamic ranges of $10^4$-$10^{10}$ within a head (suppression regime) and spread directions.
- The same optimizer fails to recover the known $n$-head representation of parity for $n\geq6$ (margins $\sim10^{-10}$), so its
  failures are not evidence; its successes are certified exactly.
- tropical.py (simulated annealing over orders and priorities): random 5-bit targets need 4-8 heads, 6-bit targets 8-10,
  7-bit targets more than 12 within the budget; the annealer stalls with a few conflicts, so these are upper estimates only.

## 13. Audit of the paper's W(n) proofs (version-5.tex, 15 November 2026)

- Theorem 3.5 (worst-case bounds). Normalization: dividing by $B_h(0)\gt0$, absorbing numerator constants into $c=S(0)\neq0$
  (strictification guarantees $c\neq0$), scaling by $1/|c|$: correct. Cleared polynomials $P_x$ have parameter degree $H$
  (the term $\sigma\prod_hB_h$ has degree $H$, each $(u_h\cdot x)\prod_{g\neq h}B_g$ has degree $1+(H-1)$): correct. Warren with
  $m=2nH\leq N-1$ polynomials... (with $N-1$ polynomials in $2nH$ variables) gives $2(2e(N-1)/n)^{2nH}=2^{1+2nHL_n}$; comparison
  with $2^N$ gives $H\geq(N-1)/(2nL_n)$ and $L_n=n-\log_2n+\log_2(2e)+o(1)$: correct. The case $2nH\gt N-1$ is handled by
  $L_n\gt1$: correct.
- Lemma (series derivative criterion) and Lemma (cube edges give the derivative rank): the identity
  $q(v\oplus e_i)-q(v)=(1-2v_i)\partial_ip(\mathbf 1+v)$ holds because $p$ is affine in each coordinate; the kernel of the
  derivative map is the space of $q$ constant on the components of $G_D$, of dimension $c(D)$; rank $2^n-c(D)$: correct.
  Connected $G_D$ gives spanning for all positive scales outside a finite set (rationality argument): correct.
- Theorem 3.7: $s(n)\leq\gamma_c(Q_n)$ and Griggs (2021, Theorem 6.1) $\gamma_c(Q_n)=(1+o(1))2^n/n$: confirmed by the survey.
- Theorem 3.8 (cancelling pairs): the identity $A_1/B_1+A_2/B_2=0$ on the cube uses $u(1-u)=0$; the $3d\times3d$ limiting
  Jacobian block is block upper triangular with invertible diagonal blocks; admissibility by adding $sC$ and nonvanishing of the
  determinant for some integer $s\geq1$ by finiteness of zeros: correct. Head count $H_{d,r}=(2^d/d)(2\lfloor2^r/3\rfloor+t_r)$ and
  the subsequence constant $2/3$: correct. The parameter count caps this mechanism at $(\tfrac12+o(1))N/n$.

## 14. Precision requirement (rigorous, elementary)

**Proposition.** Suppose a Boolean function is represented in the normalized form of Section 1 with every parameter
$\sigma,u_{h,i},b_{h,i}$ (and $v,d$) an integer multiple of $2^{-p}$ of absolute value at most $2^p$. The number of functions
representable this way with $H$ heads is at most $2^{(2nH+1)(2p+2)}$. Hence representing all Boolean functions needs
$H\geq(N-1)/(2n(2p+2))$, and any family of representations with $H\leq cN/n^2$ heads must use parameters of precision
$p\geq n/(4c)-1$ bits (equivalently dynamic range or resolution $2^{\Omega(n)}$).

**Proof.** Each parameter takes at most $2^{2p+1}+1\leq2^{2p+2}$ values, so there are at most $2^{(2nH+1)(2p+2)}$ parameter vectors, each giving one function. $\blacksquare$

So "Warren-tightness" is a statement about exponential-precision parameters: with polynomial precision $p=O(\log n)$ the
lower bound is $\Omega(N/(n\log n))$ heads, and with constant precision $\Omega(N/n)$. The paper's spanning constructions use
integer coefficients of size $O(n)$ (precision $O(\log n)$), consistent with their $N/n$ head counts; the cancelling-pair
construction uses an integer scale $s\leq N(H-1)+1$, i.e. $O(n)$ bits, which is why a parameter count rather than a precision
count limits it.

## 15. Why the univariate collapse does not extend: Chow degrees (heuristic, labelled as such)

The cleared score $P_\theta=\sigma\prod_hB_h+\sum_hA_h\prod_{g\neq h}B_g$ is a first-order perturbation of the product
$Q_\theta=\prod_hB_h$. The products of $H$ affine forms in $n$ variables form the Chow variety of completely reducible forms,
of dimension $nH$ and degree

$$ \deg\operatorname{Chow}_H(\mathbb P^n)=\frac{(nH)!}{H!\,(n!)^H}, $$

the degree of the multiplication map $(\mathbb P^n)^H\to\mathbb P(\operatorname{Sym}^H)$ divided by $H!$ (check: reducible conics
in $\mathbb P^2$ have degree $3$, triangles have degree $15$). For $n=1$ every binary form splits, so the Chow variety is the
whole space and has degree $1$: this is exactly why univariate (and common-direction) sums of simple fractions interpolate
uniquely and have a linear-like sign-pattern count. For $n\geq2$, Stirling gives

$$ \log_2\deg\operatorname{Chow}_H(\mathbb P^n)\approx(n-1)H\log_2H, $$

which for $H\asymp N/n^2$ is $\Theta(n^2H)=\Theta(N)$: the complex multiplicity of "a product (or its polarization) vanishing at
$\Theta(nH)$ prescribed points" is Warren-like. So there is no algebraic collapse once the directions spread; the open quantity is
the number of real solutions in the admissible orthant for cube points. This explains the experimental observation that the
optimizer finds genuinely nonlinear representations below the fixed-list threshold only when the directions are spread and the
dynamic ranges are large, and it leaves both conjectures standing.

## 16. Exact tropical-model complexities (SAT, CaDiCaL; see experiments/wn_search/tropical_exact.py)

Verified against brute force at n = 3 (384/384 decisions agree). T(f) = minimum number of heads in the tropical
(dominance) sub-model. Stored models use "smaller rank = higher priority"; decoding them with that convention
reproduces every target exactly (checked).

| n | random targets | mean | parity | majority | N/n^2 | N/n |
|---|---|---|---|---|---|---|
| 4 | 30 targets, values 1 to 4 | 2.9 | 6 | 4 | 1.0 | 4.0 |
| 5 | 3,5,5,3,6,4,3,4,4,4 | 4.1 | 10 | 5 | 1.3 | 6.4 |
| 6 | 5,6,7,6,6 | 6.0 | greater than 13 | greater than 7 | 1.8 | 10.7 |
| 7 | 9, 10, 11, [9,10], [10,11], [11,12], [11,12], [11,13] (8 targets, 15-minute SAT caps) | about 10.6 | | | 2.6 | 18.3 |
| 8 | [12,17] (first target; SAT at 17 took 610 s, 12 to 16 timed out), others running | | | | 4.0 | 32.0 |

Structure of the optimal solutions (correct decoding): most rules are used (22 to 28 nonempty fibers out of 30 to 42
at n = 6), fibers are small (mean 2.2 to 2.9 points, maximum 9 to 12), and the used rules sit at mean position 2.5
in their orders (dimension about n-3.5). Parity uses fibers of size 1 or 2 only (30 nonempty fibers for 31 points at
n = 5), i.e. essentially one rule per point: parity and majority are exponentially more expensive in the sub-model
than in the full model ($H^{\ast}=n$ and $1$), confirming that dominance alone cannot replace cancellation. For
random targets the mean fiber size grows slowly with n (1.9, 2.3, 2.6 at n = 4, 5, 6); an $N/n^2$ rate would need
mean fiber size proportional to n. The normalized values $Hn/N$ for the random means are $0.72, 0.64, 0.56$ and about $0.57$ at $n=4,5,6,7$ (n=7: eight targets with midpoint mean 10.6; roughly stable),
while $Hn^2/N$ grows ($2.9, 3.2, 3.4, 3.8$): within this small range the exact optima of the dominance sub-model scale like
$N/n$ with constant about $0.55$, comparable to the paper's universal bounds for the full model, not like $N/n^2$.
The greedy constructor of Section 17 is far from these optima.

## 17. Greedy tropical constructor (experiments/wn_search/tropical_greedy.py)

Random orders, priorities assigned greedily (largest monochromatic uncaught part first). Minimal H for which the greedy
finishes, random targets, 3 per n, 2 order samples:

| n | greedy H (mean) | H n^2/N | H n/N |
|---|---|---|---|
| 5 | 10.0 | 7.8 | 1.6 |
| 6 | 22.7 | 12.8 | 2.1 |
| 7 | 56.7 | 21.7 | 3.1 |
| 8 | about 95 | 23 | 2.9 |
| 9 | 186 | 29 | 3.3 |
| 10 | 340 | 33 | 3.3 |
| 11 | 686 | 41 | 3.7 |

The ratio H n/N grows from 1.6 to about 3.7 (slowly, roughly like a logarithm), so with random orders the dominance regime
is at best linear-like with a poor constant, about 3 to 4 times N/n, and the trend is away from N/n^2; the exact SAT optima at n = 5, 6 (3 to 7 heads) are much smaller only because at small n the
"catch one whole colour class, let the default rule take the other" structure is available. The schedule obstruction
(each head has one rule per dimension, and a rule of dimension d is usable only when all but about log(nH) of its points
are already caught) is visible here. Conclusion: the tropical transfer theorem is a valid tool, but the dominance regime by
itself does not approach $N/n^2$; any $N/n^2$ construction must combine dominance with cancellation at comparable scales.

## 18. Why dominance hierarchies stay linear-like (heuristic accounting)

In any dominance scheme a head is productive on a region of scale $b$ (points of a block of size $b$, or pairs inside a vertex
set of size $b$) only through a pattern with about $b\log b$ bits (an affine pattern on a block, a chain graph on a block of
pairs), so a head finalizes at most $O(b\log b)$ points of a random target there. Regions of every scale are needed, because a
region of scale $b$ can be used only after all but $O(b\log b)$ of its points were finalized at smaller scales. With the natural
nested-block hierarchy the cost of scale $\ell$ (blocks of size $2^\ell$) is (points handled at scale $\ell$)/($\ell2^\ell$).
For the weight-two miniature this is $n/(4\ell)$ heads per level, and summing over the levels $\ell\in[\ell_0,\log_2n]$ gives
$\Theta(n)$ heads, the linear-like rate, even though the top level alone would cost only $n/(4\log_2n)$ (the Warren rate).
For the cube the same accounting reproduces $\Theta(N/n)$. The exact SAT values and the greedy data (Sections 16, 17) are
consistent with this. Cancellation schemes are linear-like by dimension counting (Section 8). Hence a $2^n/n^2$ construction,
if one exists, must live in the non-perturbative regime where $\Theta(n)$ heads of comparable magnitude interact at a typical
input; this regime has no combinatorial description and its real interpolation multiplicity (Sections 11, 15) is the open
quantity.

## 19. Selezneva's XOR-of-pseudoproducts result (bibliography; full texts not reachable from the sandbox)

- S. N. Selezneva, Moscow Univ. Comput. Math. Cybern. 38(2):64-68 (2014): first bounds for the length $L^{ESPP}(n)$ of Boolean
  functions as XOR sums of pseudoproducts (products of affine functions over $\mathbb F_2$, i.e. indicators of affine subspaces).
- S. N. Selezneva, Moscow Univ. Comput. Math. Cybern. 40(3):123-127 (2016): $L^{ESPP}(n)\asymp2^n/n^2$; the abstract adds that
  $L^{ESPP}(n)$ equals the least $l$ such that every Boolean function is a mod-2 sum of at most $l$ multiaffine functions.
- S. N. Selezneva, Comput. Math. Math. Phys. 57(5):898-903 (2017): $O(k^n/n^2)$ over every finite field $\mathbb F_k$.
- Lower bound (counting): the number of affine subspaces of $\mathbb F_2^n$ is $2^{n^2/4+n/2+O(1)}$, so $L\geq(4-o(1))2^n/n^2$.
- Structural facts (derived, not quoted): the representation cost is invariant under affine substitutions (shearing is free);
  counting forces the terms to be generic flats of dimension about $n/2$; the trivial block recursion $L(n)\leq2^{n-m}L(m)$ loses a
  factor 4 per halving, so the construction must be global. The construction itself could not be read.
- Over the reals, the counting lower bound $\Omega(2^n/n^2)$ for signed sums of affine-subspace indicators persists; whether
  $O(2^n/n^2)$ is achievable with real coefficients is unknown, and in any case affine subspaces of $\mathbb F_2^n$ (parity
  constraints) are not available to single heads of the attention model (parity on $n$ bits costs $n$ heads).

## 20. Two-variable grid miniature (uninformative)

On a $12\times12$ grid in $[0,1]^2$ with heads $(u\cdot x)/(1+b\cdot x)$, the hinge search fails even at $H=36$ (numerator dimension
$73\approx P/2$), where Cover's count would predict success for a generic point set: the grid is far from general position
(the features are smooth functions of two coordinates), so this miniature does not probe Warren tightness. Recorded for
completeness; not used.

## 21. Parity in the tropical sub-model: two rigorous observations

Write rules as $(i,U)$ with subcube $\lbrace x_i=1,\ x_U=0\rbrace$; a rule is available at $x$ iff $U\subseteq Z(x)$ and
$i\in\operatorname{supp}(x)$; $\operatorname{top}(x)$ is the highest-priority available rule and the fibers of top are
the sets finalized by each rule. In a valid tropical representation of parity every fiber is an independent set of the
cube graph.

**Lemma A (swap exclusion).** No fiber contains two points $x$ and $x'=x+e_a-e_b$ ($a\in Z(x)$, $b\in\operatorname{supp}(x)$).

*Proof.* Let $\rho=(i,U)=\operatorname{top}(x)=\operatorname{top}(x')$ and $y=x+e_a=x'+e_b$. Membership of $x'$ in the subcube
of $\rho$ gives $a\notin U$ and $b\neq i$, so $\rho$ is available at $y$. Since $y$ is adjacent to $x$, parity forces
$\operatorname{top}(y)\neq\rho$, hence $\operatorname{top}(y)\succ\rho$. If $\operatorname{top}(y)=(i',U')$ were available at $x$ it would
beat $\rho$ there; as $U'\subseteq Z(y)\subseteq Z(x)$, non-availability at $x$ means $i'\notin\operatorname{supp}(x)$, i.e. $i'=a$.
The same argument from $x'$ gives $i'=b$, a contradiction since $a\neq b$. $\blacksquare$

**Lemma B (edge explanation).** For every edge $(x,x+e_m)$ of the nonzero cube, either $i(\operatorname{top}(x+e_m))=m$ or
$m\in U(\operatorname{top}(x))$. Consequently $\sum_x\big(|U(\operatorname{top}(x))|+1\big)\geq n(N-1)/2-n$, so the finalizing rules have
$|U|\geq n/2-2$ on average, and (taking $x=\mathbf 1$) at least $n-1$ heads have distinct first elements: $T(\mathrm{PARITY}_n)\geq n-1$.

*Proof.* If $m\notin U(\operatorname{top}(x))$ then $\operatorname{top}(x)$ is available at $x+e_m$ and, by the argument of Lemma A,
$\operatorname{top}(x+e_m)$ is a higher-priority rule not available at $x$, which forces $i=m$. Each point explains at most
$|U|+1$ of its incident edges (its up-directions in $U$ and its down-direction $i$), and every edge needs one explanation.
For $x=\mathbf 1$ the top rule is a half-cube $(i_1,\varnothing)$; every other direction $m$ needs
$i(\operatorname{top}(\mathbf 1-e_m))=m$, i.e. a head whose order starts with $m$. $\blacksquare$

Lemma A is machine-checked in core Lean 4 (`Tropical.Model.swap_exclusion`, `formalization/HeadComplexity/Tropical/SwapExclusion.lean`, axioms propext, Classical.choice, Quot.sound only). These match the SAT data (fibers of size one or two, $T=6,10,\geq14$ for $n=4,5,6$) but do not yet give the conjectured
$T(\mathrm{PARITY}_n)=\Omega(N/n)$; a fiber could still be a distance-four code inside a weight level.

## 22. Interpolation multiplicity: real counts versus Chow degrees (experiments/wn_search/interp_count.py)

Planted targets at $2nH$ random nonzero cube points, Levenberg-Marquardt from random starts, distinct converged real
solutions (deduplicated up to head permutation), admissible = all denominator slopes nonnegative.

| (n,H) | unknowns | starts | converged | distinct real | admissible | Chow degree $(nH)!/(H!(n!)^H)$ |
|---|---|---|---|---|---|---|
| (5,2) | 20 | 1500 | 461 | 19 | 3 | 126 |
| (5,3) | 30 | 800 | 164 | 27 | 10 | 126126 |
| (6,2) | 24 | 800 | 257 | 26 | 11 | 462 |
| (7,2) | 28 | 600 | 116 | 12 | 2 | 1716 |
| (6,3) | 36 | 600 | 53 | 12 | 2 | 2858856 |

The number of distinct real solutions found saturates (a few hundred converged runs land on a few dozen solutions), so
the real multiplicity is plausibly of order tens here, while the complex degree of the product variety jumps by a factor
$10^3$ from $(5,2)$ to $(5,3)$. If real admissible multiplicities stay polynomial in $nH$ rather than exponential, the
cell count is linear-like and $W(n)=\Omega(N/n)$ up to constants. This is suggestive evidence for the refutation side, not
a proof: the sampler can miss solutions, and the regime $H\asymp N/n^2$ is out of reach.

## 23. Neural-network capacity literature (from the third survey) and what it says about the cube

- Decision lists over subcubes: counting bound $2^n/(1.585n)$; no universal $O(2^n/n)$ bound in print; exact Shannon values
  $2,3,5,9=2^{n-1}+1$ for $n\leq4$ (attained by parity); parity has a product-lemma list of length $5^{n/3}$ and needs
  $\geq2^{n/2+1}$ rules, so for general subcube decision lists parity is exponentially harder than random functions
  (random 5-bit functions need 7-8 rules). Threshold of subcube indicators: counting $\approx1.71\cdot2^n/n$, no universal
  $O(2^n/n)$ bound found; in the $2^n$-monomial basis the density is $\Theta(2^n)$ (Oztop 2006: $\leq0.75\cdot2^n$; Amano
  2010: almost all $\leq0.617\cdot2^n$; counting $\geq0.11\cdot2^n$).
- Depth-two threshold circuits: Kane, Williams (STOC 2016) $\Omega(2^n/n^2)$ for almost all functions, trivial upper bound
  $2^{n-1}+1$, no improvement found; the gap is of exactly our type.
- Capacity of one-hidden-layer networks: Baum (1988) shows $\lceil N/n\rceil$ threshold units memorize $N$ points in general
  position; Kowalczyk (1997, Neural Networks 10:1417-1433) shows that for general-position $N$-tuples full memorization by
  $h$ threshold units forces $N\leq nh+1$, i.e. the LINEAR count is exact for generic inputs (the Warren-type $W\log W$ is not
  attained on generic point sets); Maass (1994) attains $\Omega(W\log W)$ only with two hidden layers (Boolean inputs), Sakurai
  (1993) with one hidden layer but real inputs at exponentially separated scales; Sontag (1997): shattering all general-position
  $k$-sets needs about $k/2$ parameters for broad activation classes.
- Interpretation for $W(n)$: for threshold units the linear count for generic points comes from the fact that a unit's effect on
  the rest of the network is only through its Boolean output pattern, so every unit can be moved to a vertex of its own
  arrangement independently (Cover's trick). For real-valued units (our atoms $(u\cdot x)/(1+b\cdot x)$) the contribution is a
  real number and this independence fails, which is why Warren's bound is the only general tool. Super-linear capacity for
  one-hidden-layer networks on BOOLEAN inputs is not known for any unit type we found; the Boolean cube is a highly structured
  point set, so neither the generic-position linear bound nor the special-set $W\log W$ constructions apply directly.

## 24. Kowalczyk and Sontag (details obtained; primary texts not reachable)

- Kowalczyk (Neural Networks 10, 1997): for a one-hidden-layer threshold network with $h_1$ units on a randomly selected
  $N$-tuple of points in general position, memorizing 100% of all dichotomies with probability one forces $N\leq nh_1+1$, and 50%
  forces $N\leq2(nh_1+1)$; the number of implementable dichotomies is locally constant on general-position tuples but may differ
  between tuples (no exact counting function; Mitchison, Durbin 1989 made the same point). The mechanism is Cover-type cell
  counting in the first-layer parameter space, which is specific to threshold units (a unit affects the rest of the network only
  through its Boolean pattern). It needs general position and says nothing about the Boolean cube, where the per-function
  conclusion is false (parity uses $n$ heads).
- Sontag (Neural Computation 9, 1997): for concept classes defined by certain classes of analytic functions with $n$ parameters
  there are nonempty open sets of samples of length $2n+2$ that cannot be shattered (weaker form for piecewise-analytic
  activations). The argument lets pairs of nearby points force approximate zeros at $n+1$ generic locations, impossible for an
  $n$-parameter analytic family; it concerns open sets of Euclidean samples, not a fixed combinatorial set, and bichromatic cube
  edges only force zeros somewhere on segments, which is not a codimension condition. So neither result transfers to $W(n)$.

## 25. Weight-two miniature at 64 vertices and the "all parameters count once" pattern

At n = 64 (2016 pairs) the hinge search finds a random graph with H = 8 heads (2nH = 1024, nH+1 = 513 numerator
dimensions) and fails for H <= 6. Cover's threshold for the numerators alone is H ~ 16; Warren's rate would allow H ~ 3.
Together with n = 32 (found 4, Cover 8) the certified successes sit where the TOTAL parameter count 2nH+1 is about half the
number of points, i.e. exactly as if every parameter (numerator or denominator) contributed one linear dimension: a
"linear-like with 2nH effective dimensions" picture. On the cube at n = 8 the same picture would predict about 8 heads;
the search finds 12 to 14, so there the optimizer is weaker. None of this is evidence about the asymptotics, but it is the
cleanest empirical fingerprint we have: denominators behave like extra linear parameters, not like n-bit encoders.

## 26. Longer bounded-range search at n = 8

With slopes clipped to $[10^{-1},10]$, 1500 iterations and 10 restarts, a random 8-bit function is certified with
$H=11$ heads ($nH+1=89$ numerator dimensions, $2nH+1=177$ parameters, $N=256$); $H=10$ fails with hinge loss about 1.5.
So the certified typical head count at $n=8$ is 11 to 12; the "all parameters count once" fingerprint ($2nH+1\approx N/2$,
$H\approx8$) is not reached on the cube by this optimizer, and $N/n^2=4$ is far away.
