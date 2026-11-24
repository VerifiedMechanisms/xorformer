# Radial Collision Signs Transfer to Exponential Product Atoms

## Status and model

This is a checked auxiliary theorem, not a lower bound for unrestricted head complexity. The proof was independently rechecked in this run on 2026-11-24. No Lean formalization of this note is claimed.

The original scores are $c+\sum_{h=1}^H A_h(x)/B_h(x)$ on $X=\lbrace0,1\rbrace^n$. Every numerator and denominator is affine. Every denominator is strictly positive on the cube and has slopes all strictly positive, all strictly negative, or all zero. Constant denominators retain the original restriction on numerator slopes. The transfer lemma needs only a finite input set and a positive common base.

## Fixed radial collision theorem

Let $X$ be finite. Fix real functions $B_0,A_1,\ldots,A_H,C_1,\ldots,C_H$ on $X$, with $B_0(x)\gt0$ everywhere, and fix $c\in\mathbb R$. Define

$$ R_\varepsilon(x)=c+\sum_{h=1}^H\frac{A_h(x)}{B_0(x)+\varepsilon C_h(x)},\qquad E_\varepsilon(x)=cB_0(x)+\sum_{h=1}^H A_h(x)e^{-\varepsilon C_h(x)}. $$

There exists $\varepsilon_0\gt0$ such that every denominator is positive and $\mathrm{sgn}R_\varepsilon(x)=\mathrm{sgn}E_\varepsilon(x)$ for every $x\in X$ and $0\lt\varepsilon\lt\varepsilon_0$. An identically zero germ has sign zero. Cancellation order may depend on the input.

**Proof.** Fix $x$, and write $B=B_0(x)$, $a_h=A_h(x)$, and $v_h=C_h(x)$. Introduce $a_0=cB$ and $v_0=0$, so that

$$ R_\varepsilon(x)=\sum_{h=0}^H\frac{a_h}{B+\varepsilon v_h},\qquad E_\varepsilon(x)=\sum_{h=0}^H a_he^{-\varepsilon v_h}. $$

For $k\geq0$, put $M_k=\sum_{h=0}^H a_hv_h^k$, with $v_h^0=1$. Convergent expansions near zero give

$$ R_\varepsilon(x)=\sum_{k\geq0}\frac{(-1)^kM_k}{B^{k+1}}\varepsilon^k,\qquad E_\varepsilon(x)=\sum_{k\geq0}\frac{(-1)^kM_k}{k!}\varepsilon^k. $$

Group equal values of $v_h$. If there are $r$ distinct values, the Vandermonde matrix of their powers from zero through $r-1$ is invertible. Thus either some $M_k$ with $k\leq r-1\leq H$ is nonzero, or every grouped coefficient vanishes. In the latter case both germs vanish identically. In the former case their first nonzero coefficients have the same sign, because $B^{k+1}$ and $k!$ are positive. Their signs agree for all sufficiently small positive $\varepsilon$. A finite minimum over $X$, also enforcing denominator positivity, proves the assertion. $\blacksquare$

## Affine functions give polynomial sign predicates

Assume now that $X=\lbrace0,1\rbrace^n$ and the fixed functions in the theorem are affine. Write $C_h(x)=c_{h0}+\sum_i c_{hi}x_i$ and $z_{hi}=e^{-\varepsilon c_{hi}}$. Absorbing $e^{-\varepsilon c_{h0}}$ into the numerator shows that the exponential score belongs to the family

$$ g(x)=d+\sum_{h=1}^K\left(a_{h0}+\sum_{i=1}^n a_{hi}x_i\right)\prod_{i=1}^n z_{hi}^{x_i},\qquad z_{hi}\gt0,\qquad K=H+1. $$

The additional head with every $z_{hi}=1$ supplies $cB_0$. The free bias $d$ allows exact zero entries to be assigned uniformly to either Boolean class, after preserving all nonzero signs. For fixed $x$, this is a polynomial of degree at most $n+1$ in $p=1+(2n+1)K$ parameters. When $N=2^n\geq p$, Warren's strict-sign estimate gives

$$ \left|\lbrace\text{strict sign tables of }g\rbrace\right|\leq\left(\frac{4e(n+1)N}{p}\right)^p. $$

The positive restriction on the $z_{hi}$ can only reduce the count. This invocation is a written application of the standard theorem, not a Lean verification of Warren's theorem. A primary statement is [Alon, Tools from Higher Algebra, Proposition 5.4](https://web.math.princeton.edu/~nalon/PDFS/tools1.pdf).

For $n\geq2$, $H\geq1$, and $6nH\leq N$, the inequalities $2nH\leq p\leq6nH$ yield the explicit bound

$$ \log_2\left|\lbrace\text{eventual fixed-radial labels with at most }H\text{ heads}\rbrace\right|\leq6nH\log_2(3eN/H). $$

In particular, if $n\geq16$ and $H\leq N/(32n\log_2 n)$, this logarithm is at most $3N/4$. Indeed, $h\log(3eN/h)$ is increasing in this range, and $\log_2(96en\log_2 n)\leq4\log_2 n$ for $n\geq16$. Hence some Boolean target requires more heads in this restricted class. At widths $H=\Theta(N/n^x)$ with fixed $1\lt x\lt2$, its logarithmic sign capacity is $O(nH\log n)$.

The strictifying bias is chosen after the eventual nonzero signs are established. At one sufficiently small finite value of $\varepsilon$, choose its absolute value below the minimum absolute nonzero entry. This does not permit an arbitrary moving bias that competes with the original leading terms.

## Fixed permutation fluctuations

Fix levels $\alpha_1,\ldots,\alpha_H$, permutations $\pi_1,\ldots,\pi_n$ of $[H]$, and $c\gt0$. For $S\subseteq[n]$, define

$$ T_\varepsilon(S)=\sum_{h=1}^H\frac1{c+|S|+\varepsilon\sum_{i\in S}\alpha_{\pi_i(h)}},\qquad M_\varepsilon(|S|)=H^{1-n}\sum_{u\in[H]^n}\frac1{c+|S|+\varepsilon\sum_{i\in S}\alpha_{u_i}}. $$

Unused indices in the second expression each contribute a factor $H$. Thus it equals $H$ times the independent uniform expectation over the indices in $S$. Both sums have the same positive per-input base $c+|S|$ and fixed affine shifts, so the transfer theorem applies to their difference. This finite mixture is a proof device, not a claimed head budget.

Put $z_j=e^{-\varepsilon\alpha_j}$. Its exponential mean factorizes:

$$ H^{1-n}\sum_{u\in[H]^n}\prod_{i=1}^n z_{u_i}^{x_i}=H^{1-n}\prod_{i=1}^n\left(\sum_{j=1}^H z_j^{x_i}\right)=H\left(\frac1H\sum_{j=1}^H z_j\right)^{|S|}. $$

Consequently $T_\varepsilon-M_\varepsilon$ has the eventual signs of

$$ P_\varepsilon(S)=\sum_{h=1}^H\prod_{i\in S}e^{-\varepsilon\alpha_{\pi_i(h)}}-H\left(\frac1H\sum_{j=1}^H e^{-\varepsilon\alpha_j}\right)^{|S|}. $$

This is a sum of $H+1$ product atoms. The preceding bound applies regardless of how many moments vanish. Empty and singleton inputs vanish identically; a sufficiently small negative bias assigns these zeros to the false class without changing other signs.

## Fixed Hoeffding residuals

Fix the same data and a cutoff $d\in\lbrace0,\ldots,n-1\rbrace$. Let $g^{\mathrm{rec}} _{k,j}$ be the order $j$ Hoeffding component of the kernel $(u_1,\ldots,u_k)\mapsto(c+k+\varepsilon\sum_i\alpha _{u_i})^{-1}$ under the product uniform measure. The residual is

$$ R_{d,\varepsilon}(S)=\sum_{h=1}^H\sum_{\substack{V\subseteq S\cr |V|\gt d}}g^{\mathrm{rec}} _{|S|,|V|}\bigl((\pi_i(h))_{i\in V}\bigr). $$

For each fixed input, Hoeffding projection is a finite signed combination of conditional averages, with coefficients independent of $\varepsilon$. Every reciprocal retains the same positive base $c+|S|$. Apply the moment proof to this finite combination directly; no particular head implementation of the subtraction is needed.

Set $z_{hi}=e^{-\varepsilon\alpha_{\pi_i(h)}}$ and $m=H^{-1}\sum_j e^{-\varepsilon\alpha_j}$. The product-kernel Hoeffding decomposition follows by expanding each factor as its mean plus its centered part. The corresponding exponential residual is

$$ P_{d,\varepsilon}(S)=\sum_{h=1}^H\sum_{\substack{V\subseteq S\cr |V|\gt d}}m^{|S|-|V|}\prod_{i\in V}(z_{hi}-m). $$

The two residuals have identical eventual signs on the whole cube. The polynomial displayed above has degree at most $|S|\leq n$ in the $nH$ entries $z_{hi}$ and the additional variable $m$. Treating these as independent enlarges the family. With one bias for strictifying zeros, $p=nH+2$. For $N\geq p$ and $nH\geq2$, Warren's bound gives

$$ \log_2\left|\lbrace\text{eventual fixed-cutoff radial residual labels}\rbrace\right|\leq p\log_2\left(\frac{4enN}{p}\right)\leq2nH\log_2(4eN/H). $$

Allowing the cutoff to vary adds at most $\log_2 n$. This covers deep cancellation in these fixed residuals. It does not cover arbitrary moving centering coefficients or arbitrary extra heads.

## Exact failures of uniform extension

The smallness threshold depends on the fixed coefficients. On one bit, for $0\lt\varepsilon\lt1$, take $B_0=1$, $C_1=0$, $C_2(x)=x$, $A_1=1$, and $A_2=-(1+\varepsilon+\varepsilon^2/4)$. At $x=1$,

$$ 1-\frac{1+\varepsilon+\varepsilon^2/4}{1+\varepsilon}=-\frac{\varepsilon^2}{4(1+\varepsilon)}\lt0,\qquad 1-(1+\varepsilon+\varepsilon^2/4)e^{-\varepsilon}\gt0. $$

The second inequality follows from $e^\varepsilon\gt1+\varepsilon+\varepsilon^2/2$. At $x=0$ both expressions are negative. All reciprocal denominators are admissible, and the numerator coefficients remain bounded. The numerator varies with $\varepsilon$, so this does not contradict the fixed-data theorem.

Curving only the poles also defeats the direct substitution. Use fixed weights $(1,-2,1)$ and denominators

$$ 1+\varepsilon^2x,\qquad1+(\varepsilon+\varepsilon^2)x,\qquad1+(2\varepsilon+\tfrac52\varepsilon^2)x. $$

At $x=1$, the reciprocal combination has coefficient $+1/2$ at order $\varepsilon^2$, while the combination obtained by replacing each reciprocal by the exponential of minus its increment has coefficient $-1/2$. All slopes are strictly positive. Both scores vanish at $x=0$; adding $-\varepsilon^3$ makes that input negative and preserves the disagreement at $x=1$ for sufficiently small positive $\varepsilon$.

## Exact remaining gap

No theorem here moves an arbitrary admissible representation to a fixed radial germ while preserving labels. No theorem controls arbitrary curved parameter paths with a sublinear overhead in the input dimension. Such a joint reduction would be a new mathematical mechanism. Neither near-coincidence nor compactness supplies it, as the displayed counterexamples show.
