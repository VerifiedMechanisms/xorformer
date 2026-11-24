# Independent audit of the weighted-degree sign-count theorem

## Verdict and scope

I independently checked `weighted_degree_sign_capacity.md`, including its root-count reduction, constrained-minimization argument, constants, and jet example. The written theorem is correct as stated. This is a mathematical audit, not Lean kernel verification. It does not establish the requested unrestricted head lower bound.

## Checks

**Generic thresholds and minimizers.** Choosing one witness for each of the finitely many strict sign patterns permits a common positive threshold box. Sard's theorem, applied to every active subset and threshold-sign assignment, gives simultaneous regular equality varieties and excludes more than $p$ active equalities. The objective $Q_0(z)-u\cdot z$, with $Q_0(z)=\sum_\ell z_\ell^{2\lceil D/w_\ell\rceil}$, is coercive for every $u$. Thus every closed shifted sign region has a minimizer, including unbounded regions.

**Nonsingular KKT roots.** The map from $V_{I,\tau}\times\mathbb R^j$ to $\mathbb R^p$ used in the note has equal-dimensional domain and target. A common regular value exists for the finite family by Sard's theorem. At the selected minimizer, active-gradient independence gives unique multipliers. A kernel vector of the square KKT Jacobian has its parameter component tangent to the active variety, and then lies in the kernel of the regular normal-bundle map derivative. It must vanish. Hence the selected root is nonsingular over both the reals and the complexes. Distinct full sign patterns have distinct selected parameter points, so no omitted factor of $2^m$ is needed.

**Translation and power-map root count.** A generic translation makes every coordinate of every selected root nonzero. It preserves weighted-degree bounds because the expanded monomials have coordinatewise smaller exponents. Substitution $z_\ell=y_\ell^{v_\ell}$ then gives exactly $\prod_\ell v_\ell$ distinct lifts of each selected root. Every lift is nonsingular, since the power-map Jacobian is invertible there. Ordinary affine Bezout bounds these isolated roots even if unrelated positive-dimensional components are present. This handles roots on coordinate hyperplanes before translation without any unproved multiplicity assertion.

**Degrees and constants.** Multiplier weight $3D$ makes each stationarity equation have weighted degree at most $4D-w_\ell$. The objective derivative obeys this same bound because $w_\ell\leq D$. The $j$ constraint degrees and multiplier weights contribute exactly $3^{-j}$, while active threshold signs contribute $2^j$. Consequently the sum contains $(2/3)^j\binom mj$, as stated. Replacing $4D-w_\ell$ by $4D$ and using the weighted binomial-sum estimate gives the stated constant $8e$.

## The jet limitation is substantive

For the coefficient of order $k$ of the displayed quotient, a typical term after multiplying by $B_0^{k+1}$ is $A_j B_0^{k-\ell}\prod_{r=1}^{\ell}C_{s_r}$, where $\sum_r s_r=k-j$. Under the proposed weights its weighted degree is

$$ (j+1)+(k-\ell)+\sum_{r=1}^{\ell}(s_r+1)=2k+1. $$

This verifies the example. A factorial denominator cancels a degree penalty only when sufficiently many independent variables occupy the higher weight levels. The block of order $nH$ of constant numerators and first denominator directions retains low weight. Adding all jets introduces extra parameters. No parameterization or width-preserving reduction in this note removes those costs for arbitrary finite-scale original-model representations.
