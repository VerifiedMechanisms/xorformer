# A Regular Boolean Evaluation Fiber with Different Labels

## Statement

There are two admissible three-head scores on six Boolean variables that agree at 36 specified vertices, have nonsingular 36 by 36 evaluation Jacobians at those vertices, and have different strict labels at vertex 39. Here a vertex number denotes its binary expansion with coordinate zero the least significant bit. In fact, after the same constant shift, the two label tables differ at exactly that vertex.

The 36 vertices are

$$ 1,2,3,4,5,6,7,8,9,10,11,12,13,14,16,17,18,20,21,22,23,24,25,26,28,32,33,34,36,40,45,46,48,53,57,60. $$

Both branches are regular. Consequently there is an open set of nearby 36-tuples of prescribed real scores for which two positive-denominator branches exist and retain the distinct Boolean labels. This rejects generic uniqueness of this square coordinate interpolation problem. It does not bound the number of all possible branches and does not prove any improvement to the manuscript's worst-case lower bound.

## Exact data

Write the unshifted score as

$$ T_{u,b}(x)=1+\sum_{h=1}^3\frac{\sum_{i=1}^6u_{ih}x_i}{1+\sum_{i=1}^6b_{ih}x_i}. $$

The original parameters are the following rational matrices:

$$ 24u=\begin{pmatrix}-12&-15&-27\cr-29&1&-22\cr14&8&-6\cr-10&-14&18\cr-29&-42&-33\cr-5&-31&-33\end{pmatrix},\qquad 8b=\begin{pmatrix}7&4&24\cr27&17&15\cr3&1&3\cr29&11&1\cr23&29&22\cr24&29&31\end{pmatrix}. $$

All entries of $b$ are positive. The second parameter vector is specified as the unique zero in the closed maximum-norm ball of radius $2^{-100}$ around the exact dyadic center in [the certificate](coordinate-score-fiber-certificate.json). The first 18 center entries are the numerator coefficients, followed by the 18 denominator coefficients, both in row order of the displayed matrices. Every center entry has denominator $2^{200}$. The certificate also gives an approximate inverse matrix with denominator $2^{120}$.

The final score for either model is $T-283/1024$. Its constant readout is therefore $741/1024$. The certificate and the proof below define the second model without relying on a floating-point root.

## A quantitative existence proof

Let $F:\mathbb R^{36}\to\mathbb R^{36}$ be the sampled score vector minus the original sampled score vector. Let $z_0$ be the certified center, $A$ the certified approximate inverse, and $r=2^{-100}$. All denominator slopes throughout the closed ball $K=\lbrace z:\|z-z_0\|_\infty\leq r\rbrace$ are strictly positive.

For a sample vertex with $k$ active bits, put $U_h=\sum_i u_{ih}x_i$ and $D_h=1+\sum_i b_{ih}x_i$. The exact Jacobian entries are

$$ \frac{\partial T}{\partial u_{ih}}=\frac{x_i}{D_h},\qquad \frac{\partial T}{\partial b_{ih}}=-\frac{U_hx_i}{D_h^2}. $$

For a point of $K$, both the numerator and denominator change by at most $kr$ from their center values. Set $d_h=D_h(z_0)-kr\gt0$. The change in an active numerator-column Jacobian entry is at most

$$ E_{u,h}=\frac{kr}{D_h(z_0)d_h}. $$

The change in an active denominator-column Jacobian entry is at most

$$ E_{b,h}=\frac{kr}{d_h^2}+\frac{|U_h(z_0)|kr(2D_h(z_0)+kr)}{d_h^2D_h(z_0)^2}. $$

Indeed, subtract the two reciprocal expressions, use $|D_h-D_h(z_0)|\leq kr$, and use the identity for the difference of two squares in the second expression. Summing $k(E_{u,h}+E_{b,h})$ over the three heads bounds the corresponding row sum of $DF(z)-DF(z_0)$. Let $V$ be the largest of these bounds.

The exact integer interval audit proves

$$ \eta:=\|AF(z_0)\|_\infty\lt2^{-200},\qquad q:=\|I-ADF(z_0)\|_\infty+\|A\|_\infty V\lt2^{-80}. $$

In particular, $eta\lt r/4$ and $q\lt1/4$. Define $G(z)=z-AF(z)$. The derivative bound and the fundamental theorem of calculus along segments in the convex ball give

$$ \|G(z)-G(w)\|_\infty\leq q\|z-w\|_\infty\qquad(z,w\in K). $$

Moreover,

$$ \|G(z)-z_0\|_\infty\leq q\|z-z_0\|_\infty+\eta\lt r. $$

Thus $G$ maps the complete closed ball into itself and is a strict contraction. Its unique fixed point $z^\ast$ belongs to the ball. Since $\|I-ADF(z_0)\|_\infty\lt1$, the geometric-series inverse shows that $ADF(z_0)$ is invertible. The square matrix $A$ is therefore invertible. Consequently $AF(z^\ast)=0$ implies $F(z^\ast)=0$, proving exact equality of all 36 sampled scores. The same uniform bound shows that $ADF(z^\ast)$, and hence $DF(z^\ast)$, is invertible. $\blacksquare$

## Different strict Boolean labels and openness

The verifier evaluates all 64 scores over the entire certified ball using outward integer intervals. Subtracting $283/1024$, no interval contains zero. It separately evaluates the original rational model. The two certified labels differ precisely at vertex 39, which is absent from the sample. The unshifted scores at that vertex are approximately $0.274231$ and $0.278815$; these decimals are explanatory only. The exact interval separation is recorded in [the checks](coordinate-score-fiber-checks.json).

The original Jacobian determinant reduces to 51843 modulo 65521. Every denominator used in the reduction is nonzero, so its rational determinant is nonzero. Both branches therefore have local inverse maps by the inverse function theorem. Their images contain a common open neighborhood of the original sampled value vector. The strict signs persist on sufficiently small neighborhoods of both parameter vectors, so the label disagreement persists for all sampled value vectors in a smaller common open neighborhood. This also shows that the two branches cannot be related by a head permutation.

## Integer audit and scope

[The independent verifier](verify_coordinate_score_fiber.py) uses integers only. It represents each interval by integer endpoints divided by $2^{256}$. Addition is exact at this scale. Multiplication rounds the minimum endpoint product down and the maximum endpoint product up. Division uses an outward enclosure of the reciprocal of a strictly positive interval, followed by multiplication. These rules enclose the corresponding real operations. The verifier then checks the derivative estimates, both contraction budgets, positivity on the entire ball, the original modular Jacobian determinant, and every final sign.

The numerical search and high-precision refinement only discover the certificate data. Their residuals are not premises of the existence proof. The contraction theorem and analytic assembly here are written proofs; no Lean declaration for this complete fiber theorem is claimed. This result rules out uniqueness for the specified coordinate projection. A sharper asymptotic bound on the total number of relevant coordinate branches remains a separate, unresolved theorem-strength gap.
