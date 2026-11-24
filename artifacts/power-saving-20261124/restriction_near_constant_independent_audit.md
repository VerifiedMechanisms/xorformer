# Independent audit of coordinate restriction obstructions

## Verdict

The radial/global subagent independently checked `restriction_and_near_constant_obstructions.md` on 2026-11-24. Both written constructions are correct. No Lean verification or unrestricted lower bound is claimed.

## Small-face interpolation

The reciprocal evaluation matrix is a Cauchy matrix with distinct positive parameters, followed by nonzero column scaling. Every denominator sum is positive, so its exact determinant is nonzero. Solving the resulting real linear system gives all target real tables, and constant numerators are admissible for the strictly positive nonconstant denominator slopes. Taking the positive scale arbitrarily small preserves invertibility; no bound on the interpolation coefficients is needed or assumed.

## Quantitative independence on every face

Factoring $\delta^i$ and $\delta^j$ from the two slope columns gives precisely the determinant displayed in the source note. Linearity in the remaining constant column gives $D_0+\sum_{k\in J}\delta^kD_k$ with no omitted terms.

For $i\lt j$ and increasing positive integers $h_1,h_2,h_3$, put $z_a=h_a^i$. Strict convexity of $z^{j/i}$ gives the positive orientation of the determinant with columns $1,z,z^{j/i}$. Hence $D_0\gt0$. Its entries are integers, so $D_0\geq1$.

The six determinant terms each have absolute value at most $H^{k+i+j}\leq H^{3n}$. Moreover $0\lt\delta\lt1/H\lt1$, so $\delta^k\leq\delta$ for every $k\geq1$. There are at most $n$ fixed-one coordinates. Consequently the perturbation has absolute value at most $6nH^{3n}\delta\lt1/2$. This establishes nonvanishing uniformly over all triples and all coordinate faces of dimension at least two.

The separate bound on $\delta$ gives $1\leq B_h\lt1+\eta$ on the continuous cube, and every slope is strictly positive. Thus the family remains in the original admissible denominator class. The note correctly limits its conclusion to the displayed family: it does not prohibit a different representation of the same labels with different clustering.
