# Positive Denominators Do Not Give Unique Interpolation

## Statement

This is a counterexample to a proposed auxiliary mechanism, not the requested asymptotic head lower bound.

For $x\in\lbrace0,1\rbrace^5$, consider the two-head score

$$ S_{u,b}(x)=\sum_{h=1}^{2}\frac{u_h\cdot x}{1+b_h\cdot x},\qquad b_{hi}\gt0. $$

Number the cube vertices by $v(x)=\sum_{i=1}^{5}2^{i-1}x_i$. Let

$$ I=\lbrace1,2,3,5,6,7,9,10,11,12,13,15,16,18,20,22,24,25,26,27\rbrace. $$

**Theorem.** The map $E:\mathbb R^{10}\times\mathbb R_{\gt0}^{10}\to\mathbb R^{20}$ that evaluates $S_{u,b}$ at the vertices in $I$ has two regular preimages of one value that represent different functions on the full cube. These preimages are not related by a head permutation. Both scores also vanish at the zero vertex. There is consequently a nonempty open subset of evaluation data with at least two such representations, even after quotienting by head permutations.

All denominators satisfy the manuscript's exact admissibility condition. No change to the attention model is involved.

## Explicit source and certificate

The first preimage $p_0=(u_1,u_2,b_1,b_2)$ is rational:

$$ u_1=(8,4,-18,-2,17)/10,\qquad u_2=(-12,-4,-19,12,-15)/10. $$

$$ b_1=(18,11,12,3,10)/10,\qquad b_2=(8,16,14,12,17)/10. $$

The second preimage lies in the closed coordinate box of radius $r=10^{-30}$ around the rational center $c$ in [the certificate](positive-fibers/exact-certificate.json). Every decimal string in that file denotes the exact rational number with that finite decimal expansion. Its `inverse` and `source_inverse` arrays are rational matrices $R$ and $R_0$. They are approximate inverses proposed by numerical computation; their required properties are verified by exact arithmetic below.

For orientation only, the second denominator vectors are approximately

$$ b_1=(4.2588454620,3.8242352090,1.8701216105,2.0200686301,3.1490735855),\qquad b_2=(2.0545358671,1.6952871670,0.9492242181,0.3682256935,1.4846573319). $$

The rounded display is not used in the proof.

## Proof

Put $F(p)=E(p)-E(p_0)$ and $X=\lbrace p:\lVert p-c\rVert_\infty\leq r\rbrace$. All denominator slopes throughout $X$ exceed $1/3$. In particular, $F$ is continuously differentiable on a neighborhood of $X$.

For one head, write $A=u_h\cdot x$ and $D=1+b_h\cdot x$. The Jacobian entries are

$$ \frac{\partial S}{\partial u_{hi}}=\frac{x_i}{D},\qquad \frac{\partial S}{\partial b_{hi}}=-\frac{Ax_i}{D^2}. $$

The certificate verifiers establish the following strict rational inequalities:

$$ \lVert RF(c)\rVert_\infty\lt10^{-70},\qquad \sup_{p\in X}\lVert I_{20}-RDF(p)\rVert_\infty\lt10^{-20},\qquad \lVert I_{20}-R_0DE(p_0)\rVert_\infty\lt10^{-70}. $$

Here matrix norms are the maximum absolute row sum. Define $T(p)=p-RF(p)$. The derivative bound makes $T$ a contraction on $X$, with constant less than $10^{-20}$. Also

$$ \lVert T(p)-c\rVert_\infty\lt10^{-70}+10^{-20}10^{-30}\lt10^{-30}. $$

Thus $T$ maps $X$ into itself. The contraction theorem gives a fixed point $p_\ast\in X$. The bound on $I_{20}-RDF(c)$ implies that $RDF(c)$ is invertible, hence that $R$ is invertible. Therefore $F(p_\ast)=0$.

The same bound, valid throughout $X$, implies that $DE(p_\ast)$ is invertible. The last certificate inequality implies that $DE(p_0)$ is invertible as well. Finally, the verifiers prove

$$ \bigl|S_{p}(x)-S_{p_0}(x)\bigr|\gt1/10\qquad\text{for every }p\in X\text{ at vertices }v(x)=4,8. $$

The two full-cube score functions are different. Head permutations preserve the entire score function, so they cannot account for this difference.

Apply the inverse function theorem at the two regular preimages. Intersect the resulting open neighborhoods of their common evaluation value, and shrink the parameter neighborhoods to retain positive slopes and the strict held-out separation. Every evaluation value in that intersection has two different full-cube extensions. This proves the open-set assertion. $\blacksquare$

## Independent arithmetic audits

The verifier [certify_positive_fiber.py](certify_positive_fiber.py) propagates exact rational intervals through the Jacobian and multiplies them by the rational matrix $R$.

The independent verifier [verify_positive_fiber_bounds.py](verify_positive_fiber_bounds.py) does not import that implementation or use its interval class. It proves the same inequalities using scalar derivative estimates. If $k=\sum_i x_i$ and $\delta=kr$, then throughout $X$ both $A$ and $D$ change from their center values by at most $\delta$. With $d=D(c)-\delta\gt0$, the bounds used for each active coordinate are

$$ \left|\frac1{D(p)}-\frac1{D(c)}\right|\leq\frac{\delta}{dD(c)}. $$

$$ \left|\frac{A(p)}{D(p)^2}-\frac{A(c)}{D(c)^2}\right|\leq\frac{\delta}{d^2}+\frac{|A(c)|\delta(2D(c)+\delta)}{d^2D(c)^2}. $$

The second verifier sums these derivative errors by rows and uses the induced matrix-norm inequality. Its held-out evaluation bound follows from

$$ \left|\frac{A(p)}{D(p)}-\frac{A(c)}{D(c)}\right|\leq\frac{\delta}{d}+\frac{|A(c)|\delta}{dD(c)}. $$

Both verification paths use exact integer fractions, with no floating-point comparisons. Their successful outputs are retained beside the certificate. To reproduce:

```sh
python3 artifacts/beyond-counting-bound/certify_positive_fiber.py artifacts/beyond-counting-bound/positive-fibers/exact-certificate.json
python3 artifacts/beyond-counting-bound/verify_positive_fiber_bounds.py artifacts/beyond-counting-bound/positive-fibers/exact-certificate.json
```

This proof has not been formalized in Lean. The numerical search produced the proposed center, but numerical convergence is not used as an existence premise.

## Consequence for the attempted mechanism

Positivity does not make minimal-size cube interpolation generically unique up to head permutations. A sign-counting argument cannot discard all algebraic branches on that basis. This example does not rule out a weaker bound on the number of positive branches, and it does not itself establish any asymptotic lower bound on $W(n)$.
