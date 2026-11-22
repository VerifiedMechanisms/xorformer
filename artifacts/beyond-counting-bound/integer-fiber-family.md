# An Integer Family of Regular Interpolation Ambiguities

## Statement

For every $n\geq5$, there is a set $E_n\subset\lbrace0,1\rbrace^n$ of size $4n$ such that the two-head evaluation map

$$ (u_1,u_2,b_1,b_2)\longmapsto\left(\frac{u_1\cdot x}{1+b_1\cdot x}+\frac{u_2\cdot x}{1+b_2\cdot x}\right)_{x\in E_n} $$

has at least $2^{n-4}$ regular preimages of one data vector. Every displayed preimage has integer numerators and strictly positive integer denominator slopes. They give pairwise distinct functions on the whole cube. A nonempty open set of data therefore has at least $2^{n-4}$ inequivalent positive representations.

This is an auxiliary obstruction to interpolation uniqueness. It is not a lower bound on Boolean head complexity.

## Five-bit certificate

Number vertices by $v(x)=\sum_{i=1}^5 2^{i-1}x_i$. Take

$$ E_5=\lbrace1,2,\ldots,15,16,18,23,24,31\rbrace. $$

The first parameter point is

$$ u_1=(5,0,0,-1,1),\qquad u_2=(-2,4,5,3,5),\qquad b_1=(1,3,3,2,1),\qquad b_2=(2,2,2,1,2). $$

The second is

$$ u'_1=(5,0,0,-1,2),\qquad u'_2=(-2,4,5,3,6),\qquad b'_1=(1,3,3,2,2),\qquad b'_2=(2,2,2,1,3). $$

These scores agree on $E_5$ and at vertex zero. For the first fifteen sampled vertices this is immediate because $x_5=0$. Equality at the other five vertices follows by direct rational substitution. At vertex $17$ the first score minus the second is $11/60$.

Use the parameter order $(u_1,u_2,b_1,b_2)$, with coordinates increasing inside each vector, and the displayed increasing order of sampled vertices. The two Jacobian determinants are respectively

$$ \frac{8674979}{204404136226473298939084800000000},\qquad -\frac{373618279}{53534416630743006864998400000000000}. $$

Both are nonzero. For the four rows with vertex numbers $16,18,23,31$ and the four columns $(u_{15},u_{25},b_{15},b_{25})$, the corresponding minors are

$$ -\frac7{3675375},\qquad \frac1{2138400}. $$

The exact input data are in [integer-certificate.json](positive-fibers/integer-certificate.json). The independent verifier [verify_integer_fiber.py](verify_integer_fiber.py) computes all score differences and all four determinants using rational Gaussian elimination. It uses no numerical rank tests. Its complete output is in [integer-verification.json](positive-fibers/integer-verification.json).

## Extension to every dimension

Write the first four bits as $y$ and the remaining $k=n-4$ bits as $z_1,\ldots,z_k$. Keep the first four numerator and denominator coordinates of the five-bit certificate. At every selector coordinate choose independently either of these two parameter quadruples:

$$ (u_{1j},u_{2j},b_{1j},b_{2j})=(1,5,1,2)\quad\text{or}\quad(2,6,2,3). $$

The sampling set contains all fifteen inputs $(y,0)$ with $y\neq0$. For the first selector include $(y,e_1)$ with the integer encodings of $y$ equal to $0,2,7,8,15$. For each other selector include $(y,e_j)$ with encodings $0,2,7,15$. Its size is

$$ 15+5+4(k-1)=4n. $$

Each sampled score involves at most one selector coordinate. The five-bit equalities therefore make the sampled table independent of the $k$ binary choices.

Order parameters first by the first four input coordinates and the first selector, then by the four parameters of each remaining selector. Order the sampled rows in the same blocks. The Jacobian is block lower triangular. Its first diagonal block is one of the two nonsingular $20\times20$ matrices above. Every remaining diagonal block is one of the two nonsingular $4\times4$ minors above. Hence all $2^k$ parameter points are regular.

If two choices differ at selector $j$, evaluate at $y$ of encoding one and $z=e_j$. The score difference is $11/60$, up to sign. Thus all resulting full-cube functions are different. Their denominator slopes are positive integers, so every denominator is admissible on the whole cube.

Finally apply the inverse function theorem at each of these finitely many points, intersect the open image neighborhoods, and shrink the parameter neighborhoods to preserve positivity and the finitely many strict separating score differences. This proves the open-set assertion. Head permutations preserve the full function, so they do not identify these branches. $\blacksquare$

## Audit boundary

The derivative formula used in the certificate is

$$ \frac{\partial S}{\partial u_{hi}}=\frac{x_i}{1+b_h\cdot x},\qquad \frac{\partial S}{\partial b_{hi}}=-\frac{(u_h\cdot x)x_i}{(1+b_h\cdot x)^2}. $$

The exact verifier establishes the finite arithmetic claims. Lean also checks the finite data in [IntegerFiber.lean](../../formalization/HeadComplexity/Atoms/IntegerFiber.lean). The declarations `sampled_scores_equal`, `held_out_difference`, `jacobian_det_ne_zero`, and `extension_jacobian_det_ne_zero` are in the namespace `HeadComplexity.IntegerFiber`. The determinant proofs use explicit left inverses modulo $101$ of integer matrices obtained by clearing positive row denominators. The modular identities use kernel-checked `decide`, not `native_decide`.

The block argument and inverse function theorem establish the infinite family in this written proof; that extension is not formalized in Lean. The exponential branch count is compatible with bounds of the form $C^{nH}H!$ for sufficiently large $C$, and does not establish the target asymptotic refutation.
