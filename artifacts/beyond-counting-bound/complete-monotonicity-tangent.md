# Complete Monotonicity Does Not Restrict Boolean Table Tangents

## Statement

For every $n\geq1$ there is one strictly completely monotone analytic function $E_0$ on $\mathbb R_{\geq0}^n$ whose Boolean values equal those of the single reciprocal

$$ R(S)=\frac1{1+|S|}\qquad(S\subseteq\lbrace1,\ldots,n\rbrace). $$

For every table $f:2^{\lbrace1,\ldots,n\rbrace}\to\lbrace-1,1\rbrace$, there is an affine one-parameter family of strictly completely monotone analytic functions $E_\epsilon$ such that

$$ E_\epsilon(\mathbf1_S)=R(S)+\epsilon f(S)\qquad\text{whenever}\qquad |\epsilon|\leq\frac1{4(n+1)4^n}. $$

Here strict complete monotonicity means that every mixed derivative, multiplied by the sign determined by its total order, is strictly positive. The baseline function $E_0$ is independent of $f$.

The baseline agrees with a one-head reciprocal on the Boolean cube. It is not claimed to equal that reciprocal away from the cube. The construction uses $2^n$ positive exponential terms. It does not give a representation by a bounded number of attention heads.

## Proof

Set

$$ q=\frac1{4n(n+1)2^n},\qquad K(S,T)=q^{|S\cap T|}. $$

The matrix $K$, indexed by subsets, is the tensor product of $n$ copies of the invertible two by two matrix below:

$$ K_1=\begin{pmatrix}1&1\cr1&q\end{pmatrix},\qquad K_1^{-1}=\frac1{1-q}\begin{pmatrix}-q&1\cr1&-1\end{pmatrix}. $$

Let $c=K^{-1}R$ and $d=K^{-1}f$. Since $R(S)=\int_0^1t^{|S|} dt$, tensoring the displayed inverse gives, for $k=|T|$,

$$ c_T=\frac1{(1-q)^n}\int_0^1(1-t)^k(t-q)^{n-k} dt. $$

All these coefficients are rational. More explicitly,

$$ c_T=\frac1{(1-q)^n}\sum_{j=0}^{n-k}\binom{n-k}{j}(-q)^{n-k-j}\frac{j!k!}{(j+k+1)!}. $$

At $q=0$, the integral equals

$$ \int_0^1(1-t)^kt^{n-k} dt=\frac{k!(n-k)!}{(n+1)!}=\frac1{(n+1)\binom nk}\geq\frac1{(n+1)2^n}. $$

For $t,q\in[0,1]$ and $m\geq0$, the difference-of-powers identity gives $|(t-q)^m-t^m|\leq mq$: every factor in its telescoping sum has absolute value at most one. Multiplication by $(1-t)^k$ and integration therefore change the preceding integral by at most $nq$. By the chosen value of $q$,

$$ c_T\geq\frac3{4(n+1)2^n(1-q)^n}. $$

Each row of $K_1^{-1}$ has absolute row sum at most $2/(1-q)$. Tensoring and using $|f(S)|=1$ give

$$ |d_T|\leq\frac{2^n}{(1-q)^n}. $$

Consequently, throughout the stated interval for $\epsilon$,

$$ c_T+\epsilon d_T\geq\frac1{2(n+1)2^n(1-q)^n}\gt0. $$

Now define the explicit finite exponential sum

$$ E_\epsilon(z)=\sum_{T\subseteq\lbrace1,\ldots,n\rbrace}(c_T+\epsilon d_T)\exp\left((\log q)\sum_{i\in T}z_i\right). $$

At a Boolean vertex $\mathbf1_S$, its value is $(K(c+\epsilon d))_S=R(S)+\epsilon f(S)$. The function is analytic. For a nonnegative integer multi-index $\alpha$, put $a=\sum_i\alpha_i$. Direct differentiation gives

$$ (-1)^a\partial^\alpha E_\epsilon(z)=(-\log q)^a\sum_{T\supseteq\mathrm{supp}(\alpha)}(c_T+\epsilon d_T)\exp\left((\log q)\sum_{i\in T}z_i\right). $$

Every summand is positive, $-\log q\gt0$, and the term indexed by the full set is present. This proves strict positivity for every derivative, including order zero. The baseline coefficients $c$ do not depend on $f$. $\blacksquare$

## Audit consequence

The theorem gives arbitrary Boolean sign directions at a table already represented by a single positive reciprocal. Therefore a relaxation that retains only complete monotonicity of the extended tables, even with all derivative orders and strict positivity, cannot constrain these Boolean table tangents. A usable invariant must retain additional information about the permitted affine-ratio factorization and its head budget, or require more than equality of the baseline on the Boolean inputs.

No bound on that factorization complexity follows from the construction. This order-based approach remains blocked at the required sign-counting theorem for the original heads; the main asymptotic target is unchanged and unproved.
