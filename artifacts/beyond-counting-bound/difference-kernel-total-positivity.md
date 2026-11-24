# A Zeta Obstruction to Total Positivity of Difference Weights

## Statement

The positive weight kernel in [the Boolean difference identity](boolean-difference-kernel.md) has positive minors of order two when its rates and base denominators are increasing. It is not totally nonnegative in all orders, uniformly over the number and values of the positive rates.

This is an obstruction to a variation-diminishing proof mechanism. It is not an attention-head lower bound.

## The underlying kernel

Consider $C(b,t)=1/(e^{bt}-1)$ for $b,t\gt0$. There are a positive integer $r$, increasing positive rates $b_1,\ldots,b_r$, and decreasing positive times $t_1,\ldots,t_r$ such that

$$ \det\bigl(C(b_i,t_j)\bigr)_{i,j=1}^r\lt0. $$

**Proof.** Suppose every such determinant were nonnegative. Define

$$ \Lambda(u)=\frac{e^{2u}}{e^{e^u}-1}. $$

For increasing $x_i$ and $y_j$, take $b_i=e^{x_i}$ and $t_j=e^{-y_j}$. The matrix with entries $\Lambda(x_i-y_j)$ is obtained from the matrix with entries $C(b_i,t_j)$ by multiplying rows and columns by positive numbers. Thus $\Lambda$ would be totally nonnegative. It is integrable: its decay at negative infinity is asymptotic to $e^u$, and its decay at positive infinity is faster than every exponential.

Schoenberg's characterization then supplies an entire function $\Psi$ whose reciprocal is the bilateral Laplace transform of $\Lambda$ on a strip containing zero. The precise theorem is [Gröchenig, Theorem 1(i)](https://arxiv.org/pdf/2007.12889), reporting Schoenberg's characterization of Pólya frequency functions. Substitution $v=e^u$ gives

$$ \int_{-\infty}^\infty\Lambda(u)e^{-su}du=\int_0^\infty\frac{v^{1-s}}{e^v-1}dv=\Gamma(2-s)\zeta(2-s),\qquad\mathrm{Re}s\lt1. $$

The last equality is the standard [Mellin integral, DLMF 25.5.1](https://dlmf.nist.gov/25.5.E1). Therefore the meromorphic identity theorem gives

$$ \Psi(s)\Gamma(2-s)\zeta(2-s)=1 $$

throughout the complex plane. But the zeta function has zeros $\rho$ in the open critical strip, where the gamma function is finite. At $s=2-\rho$ the left side is zero, a contradiction. Existence of such zeros is unconditional; see [DLMF 25.10(i)](https://dlmf.nist.gov/25.10.i). The argument uses no form of the Riemann hypothesis. $\blacksquare$

## Transfer to an actual finite-difference weight system

Fix a negative minor from the preceding theorem. Adjoin $R$ additional rates equal to one, where $R$ is a positive integer. Write

$$ P(t)=\prod_{i=1}^r(1-e^{-b_it}),\qquad G_R(t)=P(t)(1-e^{-t})^R,\qquad c_i(t)=\frac{b_i}{e^{b_it}-1}. $$

For the selected original rates, the weight formula gives

$$ D w_i^{(R)}(D)=\frac{\int_0^\infty e^{-Dt}G_R(t)c_i(t)dt}{\int_0^\infty e^{-Dt}G_R(t)dt}. $$

Set

$$ D_{Rj}=\frac{R}{e^{t_j}-1},\qquad \Phi_j(t)=\log(1-e^{-t})-\frac{t}{e^{t_j}-1}. $$

The $D_{Rj}$ are strictly increasing with $j$. Moreover $\Phi_j$ has a unique global maximum at $t_j$: its derivative is $1/(e^t-1)-1/(e^{t_j}-1)$, which is strictly decreasing and vanishes exactly there. Both endpoint limits of $\Phi_j$ are negative infinity. Consequently

$$ \lim_{R\to\infty}D_{Rj}w_i^{(R)}(D_{Rj})=c_i(t_j). $$

**Justification of the concentration step.** Outside any fixed neighborhood of $t_j$, $\Phi_j$ is bounded above by its maximum minus a positive constant. On a smaller neighborhood the exponent is arbitrarily close to that maximum and $P$ is bounded below by a positive constant. The tail integrals are bounded by extracting $e^{(R-1)(\max\Phi_j-\eta)}$ and integrating the remaining factors $e^{\Phi_j}P$ or $e^{\Phi_j}Pc_i$. These integrals are finite: at zero they are respectively of orders $t^{r+1}$ and $t^r$, while at infinity there is exponential decay. Dividing by the local lower bound shows that both tails are negligible. On the neighborhood, $c_i$ is uniformly as close to $c_i(t_j)$ as desired. This proves the stated limit without any interchange of a divergent integral.

The limit determinant is the negative minor above multiplied by the positive factor $\prod_i b_i$. Determinants are continuous in their entries, so for every sufficiently large integer $R$,

$$ \det\bigl(w_i^{(R)}(D_{Rj})\bigr)_{i,j=1}^r\lt0. $$

This proves the asserted failure for finite Boolean differences, not merely for an auxiliary limiting kernel. Every rate is positive. The finitely many base values can also be realized on actual Boolean inputs: choose a positive constant $d_0\lt\min_jD_{Rj}$ and add one external coordinate with slope $D_{Rj}-d_0$ for each query. Evaluating those external coordinates at singleton inputs gives exactly the required bases. All slopes of the resulting head denominator are strictly positive. $\blacksquare$

## Concrete exact-arithmetic certificates

There is a negative minor with $r=23$. Its rates are

$$ (b_i)=(8,9,10,12,13,15,17,19,22,25,28,32,36,41,46,52,59,67,76,86,97,110,125). $$

Take $t_j=\log(q_j/1000)$ with

$$ (q_j)=(2518,2259,2053,1887,1751,1639,1547,1470,1405,1350,1303,1263,1229,1199,1174,1152,1133,1117,1102,1090,1079,1069,1061). $$

Then the entries of the underlying minor are the rational numbers

$$ C_{ij}=\frac{1000^{b_i}}{q_j^{b_i}-1000^{b_i}}. $$

The verifier multiplies each row by a positive common denominator, removes a positive integer common factor, and evaluates the resulting integer determinant with fraction-free elimination. Every division is checked for zero remainder. The determinant is negative and has absolute bit length 209756. A second calculation, using outward-rounded rational interval Gaussian elimination on the original entries, also encloses the determinant strictly below zero.

For the finite-difference weights, $R=1000$ already works. Thus the full difference order is 1023, and the base values are $D_j=1000000/(q_j-1000)$. The certificate avoids a sum over exponentially many faces. Define

$$ Q_i(z)=\prod_{\ell\neq i}(1+z+\cdots+z^{b_\ell-1})=\sum_k q_{ik}z^k,\qquad m=R+r. $$

Every coefficient $q_{ik}$ is a positive integer. Substituting $z=e^{-t}$ in the integral for $F_i(D)=b_iJ_i(D)$ gives the following positive rational expression, where $(u)_k=u(u+1)\cdots(u+k-1)$ and $(u)_0=1$:

$$ \frac{F_i(D)}{\mathrm B(D,m+1)}=\frac{b_i(D)_{b_i}}{m(D+m+1)_{b_i-1}}\sum_k q_{ik}\frac{(D+b_i)_k}{(D+b_i+m)_k}. $$

Indeed, the integral is $b_i\sum_kq_{ik}\mathrm B(D+b_i+k,m)$. Dividing by $\mathrm B(D,m+1)$ and applying the beta recurrence proves the formula. These are positive column rescalings of the weight matrix. Further dividing each column by its first entry improves the arithmetic scale and preserves the determinant sign.

`verify_difference_kernel_minors.py` encloses the last normalized determinant strictly below zero using integer endpoints with common denominator $2^{1400}$. No floating-point arithmetic enters either certificate. The output is stored in `difference-kernel-minors-audit.json`.

## Audit boundary

The general kernel obstruction and its transfer through concentration are complete written proofs using the cited classical theorems. The displayed finite minors are independently reproducible external arithmetic certificates, not Lean-checked declarations. The four-bit counterexample and its actual-model realization in the preceding note are Lean checked.

The ordering invariant at order two survives. A proof requiring total nonnegativity of all higher minors is blocked by the results here. Neither these obstructions nor the number-theoretic connection establish an asymptotic lower bound for unrestricted attention-head complexity.
