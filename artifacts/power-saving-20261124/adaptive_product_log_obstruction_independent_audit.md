# Independent audit of the logarithmic adaptive product obstruction

## Verdict and scope

I independently checked `adaptive_product_compiler_logarithmic_obstruction.md`, including the prior Hall-selector proof, the exact coherent embeddings, both dimension reductions, and the sign-rank argument. The result is correct: along an unbounded sequence with $n=\Theta(H\log H)$, some strict original $H$-head targets require $\Omega(H\log n)$ affine-times-product atoms even with a free bias and arbitrary target-dependent factors.

The proof rules out a universal constant-factor adaptive compiler. It does not rule out logarithmic or sublinear polynomial overhead in $n$, and does not prove the requested worst-case head lower bound. The complete compiler obstruction is a written proof, not one end-to-end Lean declaration. The general matrix-rank ingredients were subsequently checked in a fresh independent build of `AntipodalProductRank.lean`, with only the standard foundational axioms.

## Checks

**Prior selector.** I read `artifacts/beyond-counting-bound/reciprocal-matching-shattering.md` directly from `origin/ar/7485202da367`. The affine-line union estimates prove Hall's condition with $q/2$ copies per direction. The reciprocal pair selects its assigned geometric level with main contribution $1-2/(R+1)$ and off-level contribution at most $1/(R+1)$. Therefore all desired query signs have positive integer parameter witnesses with signed margin greater than $1/2$. This is a fresh written audit of the ingredient; the prior Lean verification is provenance, not a fresh rebuild of that branch.

**One-hot coherent embedding.** All poles and witnesses are integers at least one. Hence the denominator constant one and slopes $p_{jh}-1/2$ and $\theta_h^\sigma-1/2$ are strictly positive. At a selected pair of singleton inputs, the denominator is exactly $p_{jh}+\theta_h^\sigma$. Arbitrary affine numerators are allowed because the denominators are nonconstant. The bias $\sqrt2/8$ preserves the selected signs and makes the entire cube strict, since every unperturbed value is rational.

**Polynomial-dimension level encoding.** This was independently derived during the audit. There are $L$ active level bits in every selected column. The common coefficient $1/(4L)$ contributes $1/4$, while the own-level correction contributes $\theta_h-3/4$. Together with the row contribution $p_{jh}+1/2$, the denominator is exactly $p_{jh}+\theta_h$. Every coefficient remains strictly positive. Distinct strict sign columns must have distinct level assignments. Thus all antipodal columns fit in $M+L(m+1)=\Theta(H^2)$ input coordinates.

**Rank obstruction with arbitrary factors.** An affine-times-product atom has selected matrix rank at most two across the row-column split, including with zero or negative factors. A free bias adds at most one. Antipodal completeness forces full row sign rank by the nonzero left-kernel argument. These facts impose $2K+1\geq M$ on the explicit level-encoded construction.

**Square-matrix compression.** Rank at most $r$ matrices factor through $2Mr$ real parameters, and their entries are polynomials of degree two. With $r=\lfloor M/100\rfloor$ and $M\geq100$, Warren's strict-sign bound gives at most $(4eM/r)^{2Mr}$ sign tables. Its binary logarithm is less than $22M^2/100$, hence less than $M^2$. Some square sign matrix therefore has sign rank greater than $M/100$. Applying the coherent embedding to just its $M$ columns yields $n=2M=\Theta(H\log H)$ and the claimed $\Omega(H\log n)$ product-atom requirement. This last matrix is supplied by an existence proof, not an explicit computed certificate.

## Dense-width limitation

The strongest construction has $H=\Theta(n/\log n)$. It does not concern widths comparable to $2^n$ divided by a power of $n$. More generally, a matrix flattening of an $n$-bit truth table has rank at most $2^{\lfloor n/2\rfloor}$ under a balanced split. A rank lower bound of this type alone cannot force more product atoms than an already exponential width $H\gg2^{n/2}$. A dense-width compiler obstruction would require a different invariant or a higher-order argument.
