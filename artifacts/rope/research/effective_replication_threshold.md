# An Explicit Replication Threshold for the Pure Three-Head Separation

This note makes the threshold in [Theorem 22](../../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md) effective. It uses the independently audited [quantitative tensor gap](quantitative_tensor_gap.md). This numerical strengthening is a mathematical proof, not a Lean formalization. The full existential separation remains Lean-checked.

## Statement

For every integer $m\geq10^{40000}$, the explicit classifier $f_m$ of Theorem 22 has no vanilla representation with three heads. Consequently its pure minimum is three and its vanilla minimum is between four and six.

The bound is deliberately loose. Its purpose is to supply a concrete finite threshold without an optimization claim.

## A normalized polynomial forced by a vanilla representation

Suppose a three-head vanilla representation exists. Strictify its finite Boolean scores, clear the positive denominators, and average within the eighteen replica groups as in Theorem 22. Divide the resulting nonzero polynomial by its largest absolute coefficient. This gives a polynomial $Q$ in eighteen variables of degree at most three with coefficient maximum one. It has the correct strict signs on the centered Hamming grid of mesh $2/m$. Its tensor of coefficients with one variable from each six-coordinate block still has the exact vanilla factor structure and denominator orientation.

There are $\binom{21}{3}=1330$ monomials of degree at most three. Thus on the continuous cube the sum of the absolute first derivatives of $Q$ is at most $3990$. In particular,

$$ |Q(x)-Q(x')|\leq3990\|x-x'\|_\infty\qquad(x,x'\in[-1,1]^{18}). $$

For the source polynomial $P=\sum_hN_hD_jD_k$, the coefficient sums of $N_h$ and $D_h$ are $42$ and $206$. Its coefficient absolute sum is at most

$$ 3\cdot42\cdot206^2=5346936\lt10^7. $$

Its gradient absolute sum on the cube is at most

$$ 3\left(42\cdot206^2+2\cdot42\cdot6\cdot206\right)=5658408\lt6000000. $$

## Explicit coordinates for the zero graph

Write the first three physical coordinates in each block as $a_{bi}$ and the last three as $b_{bi}$. Let $A_i=\sum_ba_{bi}$ and $B_i=\sum_bb_{bi}$. Set

$$ y_i=A_i-B_i,\qquad z_i=2\sum_j(A_j+B_j)+2A_i. $$

Retain the twelve coordinates in the last two blocks as additional coordinates $t$. The map from the eighteen coordinates $(y,z,t)$ to the physical vector $q$ is linear and rational. Its inverse formula is

$$ s=\frac{\sum_i z_i-\sum_i y_i}{7},\qquad A_i=z_i/2-s,\qquad B_i=z_i/2-s-y_i,\qquad a_{1i}=A_i-\sum_{b=2}^{3}a_{bi},\qquad b_{1i}=B_i-\sum_{b=2}^{3}b_{bi}. $$

Call this linear map $q=Mr$. Every entry of $14M$ is an integer. The largest absolute row sum of $M$ is $53/14\lt4$. In these coordinates,

$$ P=\sum_{i=1}^{3}z_i(200+y_j)(200+y_k),\qquad\lbrace j,k\rbrace=\lbrace1,2,3\rbrace\setminus\lbrace i\rbrace. $$

Use the seventeen free coordinates $(y_1,y_2,y_3,z_1,z_2,t)$ and set

$$ z_3=-\frac{(200+y_3)\bigl(z_1(200+y_2)+z_2(200+y_1)\bigr)}{(200+y_1)(200+y_2)}. $$

If every free coordinate has absolute value at most $1/1000$, then $|z_3|\lt3/1000$, and the corresponding physical zero $q_0$ has maximum norm less than $1/50$.

Shift $z_3$ by $\pm1000/m$, leaving the other affine coordinates fixed. The resulting physical points $q_\pm$ satisfy $\|q_\pm-q_0\|_\infty\leq1000/m$. Since $m\geq2000$, they and their nearest centered-grid points lie inside the continuous cube. Changing $z_3$ changes $P$ by precisely

$$ \pm\frac{1000}{m}(200+y_1)(200+y_2), $$

whose absolute value is greater than $39601000/m$. Rounding each physical coordinate to the nearest grid value changes $P$ by less than $6000000/m$. Hence the two rounded grid points have opposite strict source signs. Their $Q$ signs agree with these signs. The Lipschitz bound for $Q$ therefore implies

$$ |Q(q_0)|\leq\frac{3990\cdot1001}{m}\lt\frac{4000000}{m}. $$

This holds at every zero graph point whose seventeen free coordinates lie in the small box.

## Clearing the substitution and bounding its coefficients

For a degree-at-most-three polynomial $Q$, first form $R(r)=14^3Q(Mr)$. Substitute the displayed zero graph into $R$ and multiply by $(200+y_1)^3(200+y_2)^3$. Denote the resulting polynomial in seventeen free variables by $\mathcal A(Q)$. It has total degree at most nine. The map from the 1330 coefficients of $Q$ to its coefficients is linear with integer entries.

Every entry of this linear map has absolute value less than $10^{23}$. Here is a direct bound. A basis monomial of degree $d\leq3$, after multiplying by $14^3$ and substituting $M$, has coefficient absolute sum at most $14^{3-d}56^d\leq56^3\lt200000$. A monomial containing $z_3$ to exponent $r\leq3$, after clearing the zero substitution, has coefficient absolute sum at most

$$ 201^{6-2r}(2\cdot201^2)^r=2^r201^6\lt10^{15}. $$

Their product is less than $10^{23}$.

On the small box the previous zero-graph estimate gives

$$ |\mathcal A(Q)|\leq14^3 201^6\frac{4000000}{m}\lt\frac{10^{25}}m. $$

Choose ten equally spaced nodes in $[-1/1000,1/1000]$ for each free coordinate. The node spacing is $1/4500$. Each univariate Lagrange basis polynomial has coefficient absolute sum at most

$$ (1001/1000)^9 4500^9\lt2\cdot4500^9\lt10^{34}. $$

The sum of these bounds over the ten nodes is less than $10^{35}$. Tensor-product interpolation in seventeen variables, valid since the degree in each variable is at most nine, now bounds every coefficient of $\mathcal A(Q)$ by

$$ \frac{10^{25}}m(10^{35})^{17}=\frac{10^{620}}m. $$

## An integer minor forces proximity to the source polynomial

The kernel of $\mathcal A$ on degree-at-most-three polynomials is exactly the line spanned by $P$. Indeed, vanishing of the cleared substitution means vanishing on the open zero graph. In the fraction field of the other seventeen variables, the source is a nonzero scalar times a monic linear polynomial in $z_3$. The zero-substitution identity therefore gives divisibility there. The source is primitive and irreducible, so Gauss's lemma gives divisibility in the polynomial ring. Since $P$ has degree three, the quotient is constant. Conversely $P$ plainly has zero substitution. Thus the integer matrix of $\mathcal A$ has rank 1329.

Choose a source coefficient $P_j\neq0$. Deleting column $j$ leaves 1329 independent columns. Choose 1329 rows giving a nonsingular square submatrix. Its determinant is a nonzero integer and has absolute value at least one. Every cofactor has absolute value at most

$$ 1328!(10^{23})^{1328}\lt10^{35856}. $$

The absolute row sums of its inverse are consequently less than $10^{35860}$.

Set $\lambda=Q_j/P_j$. The $j$-th coefficient of $Q-\lambda P$ is zero, and $\mathcal A(Q-\lambda P)=\mathcal A(Q)$. Applying the inverse bound to the selected rows gives

$$ \|Q-\lambda P\|_{\mathrm{coeff},\infty}\lt\frac{10^{36480}}m\lt\frac{10^{36500}}m\leq10^{-20}. $$

Since $Q$ has coefficient maximum one and $P$ has coefficient maximum less than $10^7$, this implies

$$ |\lambda|\gt\frac1{2\cdot10^7}. $$

The all-ones centered vector belongs to every grid, and $P(\mathbf1)=5040000$. Therefore $Q(\mathbf1)\gt0$. A negative $\lambda$ would give $\lambda P(\mathbf1)\lt-0.252$, whereas the value of $Q-\lambda P$ there has absolute value at most $1330\cdot10^{-20}$. This is impossible. Hence $\lambda\gt0$.

## The tensor gap gives the contradiction

Divide $Q$ by $\lambda$. Its retained mixed tensor still has the vanilla three-head factor form, because positive scaling may be absorbed in the numerator coefficients. Its entrywise distance from the source tensor is at most the coefficient distance

$$ \left\|\frac Q\lambda-P\right\|_{\mathrm{coeff},\infty}\lt2\cdot10^7\cdot10^{-20}=2\cdot10^{-13}\lt10^{-10}. $$

This contradicts the quantitative tensor gap. Therefore no such three-head vanilla representation exists for any $m\geq10^{40000}$. $\blacksquare$

The same threshold, together with the exact dummy-input padding results, gives a separating Boolean classifier at every input length at least $18\cdot10^{40000}$. This numerical bound is a mathematical strengthening of the Lean-checked existential threshold; no assertion is made that these enormous constants are sharp or useful computationally.
