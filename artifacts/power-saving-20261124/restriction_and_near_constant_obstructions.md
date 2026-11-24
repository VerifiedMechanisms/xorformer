# Coordinate restrictions and near-constant denominators

## Scope

Two exact constructions limit proposed simplifications by coordinate restriction. Near-constant denominators do not prevent arbitrary interpolation on a sufficiently small face, and a restriction need not create exact pencil clusters. These are obstructions to particular reductions. They do not bound unrestricted Boolean sign capacity.

## Arbitrary small-face interpolation

Fix a $k$-bit cube with $m=2^k$ vertices. Choose a positive affine form $C$ with strictly positive slopes and distinct cube values, for example

$$ C(x)=1+\sum_{i=1}^k2^{i-1}x_i. $$

Choose $m$ distinct positive real numbers $s_h$. For every $\varepsilon\gt0$, use denominators

$$ B_h(x)=1+\varepsilon s_h C(x). $$

The square evaluation matrix of their reciprocals is invertible. Indeed,

$$ \frac1{1+\varepsilon s_h C(x)}=\frac{1/s_h}{1/s_h+\varepsilon C(x)}, $$

so it is a Cauchy matrix with distinct row parameters and distinct column parameters, followed by nonzero column scaling. Its determinant is nonzero because the Cauchy determinant is the product of the row differences and the column differences divided by the product of all positive pairwise sums.

Therefore arbitrary real values at all $m$ vertices are represented exactly by these $m$ reciprocals with real constant numerator coefficients. Every denominator is admissible in the original model. By taking $\varepsilon$ sufficiently small, all denominators are uniformly arbitrarily close to one. The interpolation coefficients can be unbounded as $\varepsilon$ tends to zero, which is permitted by the original model.

Thus when a restricted face has at most as many vertices as available heads, near-constancy alone cannot restrict its Boolean labels. A global argument exploiting shared parameters across many faces is not excluded.

## No three denominators share a pencil on any nontrivial face

For every $n\geq2$, $H\geq3$, and $\eta\gt0$, there are $H$ coherent strictly positive affine denominators $B_h$ satisfying

$$ 1\leq B_h(x)\leq1+\eta\qquad(x\in[0,1]^n) $$

such that, on every coordinate face with at least two free coordinates, any three restricted denominator forms are linearly independent. In particular, every exact pencil cluster in the displayed restricted family has size at most two.

**Construction.** Number the heads by $1\leq h\leq H$ and the coordinates by $1\leq i\leq n$. Choose

$$ 0\lt\delta\lt\min\left\lbrace\frac1H,\frac{\eta}{nH},\frac1{12nH^{3n}}\right\rbrace,\qquad B_h(x)=1+\sum_{i=1}^n(\delta h)^ix_i. $$

Every slope is strictly positive. Since $\delta H\lt1$, the nonconstant sum is at most $n\delta H\lt\eta$, proving the asserted range.

Fix a face, let $J$ be its coordinates fixed to one, and choose any two distinct free coordinates $i\lt j$. Its restricted constant coefficient is

$$ c_h=1+\sum_{k\in J}\delta^kh^k. $$

For three heads $h_1\lt h_2\lt h_3$, consider the three by three coefficient minor with columns consisting of the constant term and the slopes in coordinates $i,j$. Its determinant is

$$ \delta^{i+j}\left(D_0+\sum_{k\in J}\delta^kD_k\right),\qquad D_k=\det\bigl(h_a^k,h_a^i,h_a^j\bigr) _{a=1}^3. $$

Here $D_0$ is a positive integer. To see positivity, put $z_a=h_a^i$; the third column is $z_a^{j/i}$. The function $z\mapsto z^{j/i}$ is strictly convex on the positive real axis, so its consecutive secant slopes are strictly increasing, which makes the determinant positive. Since all entries are integers, $D_0\geq1$.

For $1\leq k\leq n$, the determinant expansion gives $|D_k|\leq6H^{k+i+j}\leq6H^{3n}$. Hence

$$ \left|\sum_{k\in J}\delta^kD_k\right|\leq6nH^{3n}\delta\lt\frac12. $$

The minor is therefore nonzero. This proves the claim simultaneously for every face and every triple, without a genericity assumption. $\blacksquare$

The construction concerns the displayed denominator family. It does not exclude a different representation of its target signs with fewer clusters, and it does not make near-constant representations hard by itself.

## Verification boundary

These are elementary written proofs. No Lean formalization or numerical calculation is claimed. The first construction uses the exact Cauchy determinant. The second replaces a generic avoidance argument with an explicit quantitative moment-curve construction.
