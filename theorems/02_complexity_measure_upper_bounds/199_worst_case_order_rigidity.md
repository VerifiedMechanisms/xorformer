# Rigidity Theorems For The Order Of The Worst-Case Head Complexity

## Statement

Let $N=2^n$ and $W(n)=\max_f H^{\ast}(f)$. The paper in the companion package proves $(\tfrac12+o(1))N/n^2\leq W(n)\leq(1+o(1))N/n$ and leaves the order of $W(n)$ open. This note records three rigorous statements that locate the obstruction to a $2^n/n^2$ upper bound, together with a transfer theorem for a combinatorial sub-model.

**Theorem 1 (normalized scores and where the information sits).** Every $H$-head score equals, on the cube,

$$ S(x)=\sigma+\sum_{h\in P}\frac{u_h\cdot x}{1+b_h\cdot x}+\sum_{h\in M}\frac{v_h\cdot(\mathbf 1-x)}{1+d_h\cdot(\mathbf 1-x)},\qquad b_h,d_h\in\mathbb R^n_{\geq0}, $$

up to one additional affine head. For a fixed list of denominators at most $2\sum_{i\leq nH}\binom{N-1}{i}$ Boolean functions are realizable. With $H=cN/n^2$ this is $2^{(cN/n)\log_2(en/c)+O(1)}=2^{o(N)}$, so a representation of every Boolean function with $cN/n^2$ heads must use target-dependent denominators carrying $N(1-o(1))$ bits in their $nH$ real parameters.

**Theorem 2 (common-direction collapse).** If every denominator has the form $1+t_h\beta\cdot x$ for one fixed $\beta\in\mathbb R^n_{\geq0}$ (or every denominator has the form $1+t_h\beta\cdot(\mathbf 1-x)$), then every sign-represented function is a sign pattern of a fixed linear space of dimension at most $(n+1)H+1$. Consequently at most $2\sum_{i\leq(n+1)H+1}\binom{N-1}{i}$ functions are representable by such lists, and representing every Boolean function, or a fraction of them bounded away from zero, requires $H\geq(\tfrac12-o(1))N/(n+1)$.

**Theorem 3 (tropical transfer).** Let head $h$ carry a permutation $\pi_h$ of $[n]$, integers $w_{h,1},\dots,w_{h,n}$ that are distinct over all $nH$ pairs, and signs $c_{h,k}$. For $x\neq0$ let $k_h(x)$ be the $\pi_h$-position of the first element of $\operatorname{supp}(x)$, and let $T(x)=c_{h^{\ast},k_{h^{\ast}}(x)}$ where $h^{\ast}$ maximizes $w_{h,k_h(x)}$. If $T(x)=2f(x)-1$ for all $x\neq0$ then $H^{\ast}(f)\leq H$.

> **Interpretation.** Theorem 2 says that the degree-$H$ factor in Warren's bound, which is the whole difference between $N/n^2$ and $N/n$, is illusory unless the denominator directions spread. Theorem 3 identifies the regime of exponentially spread denominators with decision lists over the subcubes $\lbrace x_{\pi_h(k)}=1,\ x_{\pi_h(j)}=0\ (j\lt k)\rbrace$; that sub-model has at most $2^{nH(n+1)}$ members, so it is counting-compatible with $N/n^2$, but it computes parity only with about $N$ rules.

## Proof

### Theorem 1. Normalization and the fixed-list count

**Proof.** Divide a positive-slope atom by $B_h(0)\gt0$ and write $A_h/B_h=A_h(0)+(u_h-A_h(0)b_h)\cdot x/B_h$; the constants $A_h(0)$ join $\sigma$. A negative-slope atom $A/(b_0+b\cdot x)$ with $b\leq0$ and $b_0+\sum_ib_i\gt0$ equals, with $y=\mathbf 1-x$, the atom $A/\big((b_0+\sum_ib_i)+\sum_i|b_i|y_i\big)$, which has positive slopes in $y$; normalize as before. A zero-slope atom is affine and is absorbed as in the proof of the normal form theorem. For fixed denominators the score is linear in $(\sigma,u,v)$, so the realizable functions are halfspace dichotomies of $N$ points in $\mathbb R^{1+nH}$, at most $2\sum_{i\leq nH}\binom{N-1}{i}$ of them (Cover). Using $\binom{N-1}{i}\leq(eN/i)^i$ with $nH=cN/n$, the count is at most $2^{(cN/n)\log_2(en/c)+O(1)}$, which is $2^{o(N)}$. Since the set of realizable functions is the union over lists of these pattern sets, $2^N$ realizable functions require $2^{N-o(N)}$ distinct pattern sets, hence $N(1-o(1))$ bits of information in the list. $\blacksquare$

### Theorem 2. Common-direction collapse

**Proof.** Put $s=\beta\cdot x$ and $Q(s)=\prod_h(1+t_hs)\gt0$. Then

$$ Q\cdot S=\sigma Q(s)+\sum_{h}\Big(a_{h,0}+\sum_ia_{h,i}x_i\Big)\prod_{g\neq h}(1+t_gs). $$

Each product $\prod_{g\neq h}(1+t_gs)$ is a polynomial of degree at most $H-1$ in $s$, and $Q$ has degree $H$, so $Q\cdot S$ lies in

$$ \mathcal W=\Big\lbrace R_0(s)+\sum_{i=1}^nx_iR_i(s):\ \deg R_0\leq H,\ \deg R_i\leq H-1\Big\rbrace, $$

a linear space of dimension at most $(H+1)+nH$. Since $Q\gt0$, the sign patterns of the family are sign patterns of $\mathcal W$. A linear space of dimension $D$ has at most $2\sum_{i\leq D}\binom{N-1}{i}$ sign patterns on $N$ points, which is less than $2^N$ unless $D\geq(N-1)/2$ and is $o(2^N)$ unless $D\geq N/2-O(\sqrt N)$. The complemented case is identical with $y=\mathbf 1-x$. $\blacksquare$

### Theorem 3. Tropical transfer

**Proof.** Let $L=2\max_{h,k}|w_{h,k}|+2$ and define exponents $m_{h,\pi_h(k)}=kL$ and $e_{h,\pi_h(k)}=kL+w_{h,k}$; both are increasing along $\pi_h$ and consecutive values differ by at least $L/2$. Put $b_{h,i}=K^{m_{h,i}}$ and $u_{h,i}=c_{h,\pi_h^{-1}(i)}K^{e_{h,i}}$ for an integer $K\gt4nH$. Fix $x\neq0$, let $k=k_h(x)$ and $t=\pi_h(k)$. Every other element of the support is later in $\pi_h$, so its exponents are smaller by at least $L/2$; hence

$$ u_h\cdot x=c_{h,k}K^{e_{h,t}}(1+\epsilon_h),\qquad 1+b_h\cdot x=K^{m_{h,t}}(1+\epsilon_h'),\qquad |\epsilon_h|,|\epsilon_h'|\leq nK^{-L/2}+K^{-L}\leq\tfrac1{4nH}, $$

and the ratio is $c_{h,k}K^{w_{h,k}}(1+\delta_h)$ with $|\delta_h|\leq1/(nH)$. The maximizing head has weight at least one larger than every other head, so its term exceeds the sum of the absolute values of all the others, which is at most $(H-1)K^{w^{\ast}-1}(1+1/(nH))\lt K^{w^{\ast}}/2$. Thus the sign of $\sigma+\sum_hu_h\cdot x/(1+b_h\cdot x)$ is $T(x)$ for every $x\neq0$ once $|\sigma|$ is smaller than $K^{\min w}/2$; take $\sigma=\pm K^{\min w}/4$ with the sign $2f(0)-1$. All slopes are positive, so the normal form theorem realizes the score with $H$ heads. $\blacksquare$

### Remarks

1. The paper's spanning lists use $N/n$ distinct directions, so Theorem 2 does not affect them; it rules out the sub-approach "fix one direction, vary scales and numerators".
2. In the tropical model each fiber of the finalizing rule is a subcube minus earlier subcubes. For parity such a fiber must be an independent set of the cube graph, which forces the first rule to be a single point and inductively about $N$ rules; so the sub-model does not contain the cancellation mechanism that gives $H^{\ast}(\mathrm{PARITY}_n)=n$.
3. A mechanism in which $k$ heads dominate a cell $R$ realizes at most $2(e|R|/(2nk))^{2nk}$ patterns on $R$ (Warren on the restricted problem), so all patterns on $R$ need $|R|\leq2nk\log_2(e|R|/(2nk))$: reaching $n^2/c$ points per head forces $|R|\geq2nk\,2^{n/(2c)}$. Dominant-cell constructions with polynomial-size cells are capped at order $N/n$.

## Consequence

The open question $W(n)=O(2^n/n^2)$ is equivalent to a Warren-tight dependence of the sign pattern on the denominator parameters. The three statements above exclude common-direction lists, dominant polynomial-size cells, and (through the parameter count) regular-zero exact representations as routes; the tropical sub-model is counting-compatible and remains the only identified candidate mechanism, with the caveat of Remark 2. The status is recorded in `notes/wn_order_notes.md` and in `artifacts/wn_order/wn_order_section.tex`.
