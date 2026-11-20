# Audit of the worst-case results in version-5.tex (15 November 2026)

All statements below were re-derived from the source; "correct" means the argument as written is complete.

## Theorem 3.5 (worst-case head complexity)

- Normalization. Starting from a strict score, each denominator is divided by its positive value at zero and each
  numerator is rewritten as $a_{h,0}B_h+u_h\cdot x$; the constants $a_{h,0}$ and the readout constant collapse into
  $c=S(0)$, which is nonzero because the score is strict at $x=0$; scaling by $1/|c|$ gives $\sigma=\pm1$. Correct.
- Cleared polynomials. $P_x=\sigma\prod_h(1+b_h\cdot x)+\sum_h(u_h\cdot x)\prod_{g\neq h}(1+b_g\cdot x)$ has total degree
  at most $H$ in the $2nH$ parameters (each factor is affine in the parameters). Correct.
- Warren's theorem. Applied to $N-1$ polynomials of degree $H$ in $2nH$ variables with $2nH\leq N-1$; the bound
  $2(4eH(N-1)/(2nH))^{2nH}=2^{1+2nHL_n}$ with $L_n=\log_2(2e(N-1)/n)$. The factor two accounts for the two values of
  $\sigma$. Correct. The case $2nH\gt N-1$ is handled by $L_n\gt1$. Correct.
- Conclusion $W(n)\geq(N-1)/(2nL_n)$ and $L_n=n-\log_2n+\log_2(2e)+o(1)$, hence $(\tfrac12+o(1))N/n^2$. Correct.
- Remark in the text: the parameter degree $H$ cannot be replaced by $n$ because $P_{e_1}$ contains the monomial
  $\sigma\prod_hb_{h,1}$. Correct, and this is exactly the degree factor whose tightness is the open question.

## Lemma (series derivative criterion) and Lemma (cube edges give the derivative rank)

- The coefficient of $x_S$ in $x_i/(1+\varepsilon a\cdot x)$ is $(-\varepsilon)^{|S|-1}(|S|-1)!\prod_{j\in S\setminus i}a_j+O(\varepsilon^{|S|})$.
  Correct (the first contributing power is $q=|S|-1$, the factors must supply the distinct variables of $S\setminus i$ in any order).
- The derivative matrix $J$ has rank $2^n-c(D)$: the identity $q(v\oplus e_i)-q(v)=(1-2v_i)\partial_ip(\mathbf 1+v)$ holds for
  multilinear $p$ because $p$ is affine in each coordinate; the kernel consists of the $q$ constant on components of $G_D$.
  Correct. Connectedness of $G_D$ therefore gives spanning for all positive scales outside a finite exceptional set
  (nonvanishing of a rational determinant). Correct.

## Theorem 3.7 (asymptotically optimal spanning)

- $s(n)\leq\gamma_c(Q_n)$ by the previous lemma, $s(n)\geq\lceil(2^n-1)/n\rceil$ by dimension. Correct.
- Griggs (INTEGERS 21A, 2021, Theorem 6.1): $\gamma_c(Q_n)=(1+o(1))2^n/n$, via Kabatyanskii and Panchenko for
  $\gamma(Q_n)$ and an expansion construction. Confirmed by the survey. Small exact values computed this run:
  $\gamma_c(Q_n)=1,2,4,6,10,16$ for $n\leq6$ and $24\leq\gamma_c(Q_7)\leq28$.

## Theorem 3.8 (cancelling pairs)

- The pair identity $A_1/B_1+A_2/B_2=0$ on the cube: with $A_1=1-u$, $A_2=-(1-u)$, $B_2-B_1=-(d-2)u$, the identity
  holds because $u(1-u)=0$ at every cube point. Correct.
- Jacobian columns: denominator directions of head one on $Z_0$, numerator directions of head one on $Z_1$, numerator
  directions of head two on $Z_2$; after scaling by $s^2$, $s$, $s$ the limit is block upper triangular with invertible
  diagonal blocks. Correct. The second head's denominator directions are proportional to the first head's on $Z_0$ and
  vanish on $Z_1\cup Z_2$, which is why the pair uses $3d$ of its $4d$ parameters; this caps the mechanism at $2/3$ of
  the parameter-count bound $(\tfrac12+o(1))N/n$.
- Admissibility by adding $sC$ with large coefficients and nonvanishing of the determinant for some integer $s\geq1$
  (finitely many zeros of a nonzero rational function). Correct.
- Head count $H_{d,r}=(2^d/d)(2\lfloor2^r/3\rfloor+t_r)$ and $W(2^k+k)\leq(\tfrac23+O(k/2^k))2^n/n$. Correct.

## Proposition 3.11 (dual criterion)

- The feature map $\phi_B$ and Gordan's alternative: correct. The remark that the weights cannot be chosen independently
  of the list (because a spanning list exists) is correct.

## Net assessment

The paper's bounds $(\tfrac12+o(1))2^n/n^2\leq W(n)\leq(1+o(1))2^n/n$ are correct as stated. The upper bounds are all
exact-representation arguments (dimension-limited to $(N-1)/(2n)$ with target-dependent denominators and $(N-1)/n$
with fixed lists); the lower bound is Warren's count. Nothing in the paper, and nothing found in the literature, decides
whether the degree factor in Warren's count is attained.
