# Replication and exact distinct-group cubic coefficients

## Scope

This appendix establishes the averaging step needed to turn a quantitative cubic coefficient obstruction into a finite Boolean obstruction. It does not by itself choose a sufficient replication count or prove the quantitative sign-rigidity estimate. Those are separate inputs.

The identities `ThreeHeadReplication.coefficient_sum_three_groups` and `ThreeHeadReplication.uniform_group_sum` are checked in `formalization/HeadComplexity/Polynomial/ThreeHeadReplication.lean`. The permutation averaging and finite-population formulas are now checked in `Polynomial/MeanGridSymmetrization.lean` and `Polynomial/MeanGridCubic.lean`. In particular, `MeanGridCubic.cubic_mean_polynomial_exists` constructs the degree-at-most-three polynomial for every arbitrary, untied raw cubic; `cubic_mean_sign_exists` proves its sign agreement on the full mean grid. The distinct-group coefficient identification with the polynomial so constructed is justified below, while the separate group-sum factorization identity is formalized.

## Replicated pure function

Let the base dimension be $n$, and replicate every coordinate $m\geq3$ times. Write the Boolean inputs in sign coordinates as $z_{i,r}\in\lbrace-1,1\rbrace$ and their group means as

$$ t_i=\frac1m\sum_{r=1}^m z_{i,r}. $$

Suppose a pure atom has positive token weights $a_{h,i},b_{h,i}$, positive query weight $\gamma_h$, query numerator $\eta_h$, and token values $v_{0,h},v_{1,h}$. Replace each token weight by $a_{h,i}/m,b_{h,i}/m$, leaving the query parameters and token values unchanged. Every weight remains positive. Its denominator and numerator on the replicated cube equal the corresponding original affine expressions evaluated at the means $t$ in centered coordinates.

In particular, the fourteen-coordinate rational construction in `README.md` gives the replicated score

$$ R_m(z)=\sum_{h=0}^2\frac{S_h(t)}{1+B_h(t)},\qquad F(t)=\sum_{h=0}^2S_h(t)\prod_{j\neq h}(1+B_j(t)). $$

Since $\sum_i|b_{h,i}|\lt1$, all three denominators are positive throughout the continuous cube. Thus the explicit Boolean formula $f_m(z)=[F(t)\gt0]$ is represented by the three displayed pure atoms on every replicated input, including inputs where $F(t)=0$. This is an algebraic full-cube sign identity, not a numerical fit.

The finite-position scalar-to-rotation bridge in Theorem 14 realizes these atoms in the specified pure architecture with fixed query token and token-only values. The dimension may be large, but is finite whenever $m$ is finite.

## Averaging an arbitrary vanilla representation

Assume an arbitrary vanilla three-head model represents $f_m$. The exact scalar-to-architecture equivalence extracts three admissible affine fractions with positive denominators on the Boolean cube. Multiplying the score by the product of these denominators gives a real polynomial $P(z)$ of total degree at most three, with

$$ P(z)\gt0 \Longleftrightarrow f_m(z)=1. $$

Reduce powers using $z_{i,r}^2=1$ to obtain its multilinear representative $P_{\mathrm{ml}}$, still of degree at most three and with exactly the same cube values. Average this polynomial over all independent permutations of the $m$ coordinates inside each of the $n$ groups. The result has a polynomial expression $Q(t)$ of total degree at most three in the group means.

To see this expression directly, the average of a product of zero, one, two, or three distinct coordinates within a group of mean $t$ is respectively

$$ E_0(t)=1,\qquad E_1(t)=t,\qquad E_2(t)=\frac{mt^2-1}{m-1},\qquad E_3(t)=\frac{m^2t^3-(3m-2)t}{(m-1)(m-2)}. $$

The second identity follows by squaring the coordinate sum. The third follows by cubing it and separating the terms with three distinct indices from those with repeated indices. Independent group permutations make the average of a multilinear monomial the product of the corresponding $E_j$ factors.

Every input with a specified group-mean vector belongs to the same permutation orbit. The target function is constant on that orbit. Consequently, whenever $F(t)\gt0$, all summands in the average are strictly positive and $Q(t)\gt0$. Whenever $F(t)\leq0$, all summands are nonpositive and $Q(t)\leq0$. This handles the model's strict-positive decision rule and all target zeros without a strictification assumption.

There are positive target inputs, so $Q$ is not the zero polynomial. It may therefore be divided by its positive maximum coefficient magnitude, preserving both sign implications.

## Exact cubic factorization on distinct groups

For three distinct groups $i,j,k$, the coefficient of $t_it_jt_k$ in $Q$ is exactly the sum of the coefficients of $z_{i,r}z_{j,s}z_{k,u}$ in the original raw cleared polynomial $P$ over all replica indices $r,s,u$.

Indeed, such a raw cubic monomial has no repeated coordinate, so multilinear reduction leaves it unchanged. Any other raw monomial of degree at most three involves at most two distinct groups, so neither reduction nor permutation averaging can produce a term involving all three groups. Finally, averaging the relevant monomial gives exactly $t_it_jt_k$, with no factor depending on $m$.

Write the centered raw numerator and denominator slope arrays as $A_{h,i,r}$ and $B_{h,i,r}$. Define their group sums by

$$ \overline A_{h,i}=\sum_r A_{h,i,r},\qquad \overline B_{h,i}=\sum_r B_{h,i,r}. $$

Trilinearity of the cubic coefficient then shows that the distinct-group cubic coefficients of $Q$ are the squarefree coefficients of the raw cubic

$$ T(t)=c\prod_{h=0}^2\overline B_h(t)+\sum_{h=0}^2\overline A_h(t)\prod_{j\neq h}\overline B_j(t). $$

This is the exact identity formalized by `coefficient_sum_three_groups`. The readout constant $c$ contributes the first term; all affine numerator and denominator constants contribute only degrees at most two and therefore do not enter this identity. The readout term may also be absorbed into one numerator direction by replacing $\overline A_0$ with $\overline A_0+c\overline B_0$.

Every denominator direction of an admissible vanilla head is strictly positive at all coordinates, strictly negative at all coordinates, or identically zero. Each nonempty group sum has the same respective property. Therefore the cubic $T$ belongs to the same all-admissible vanilla class as in the coefficient-closure obstruction, regardless of how asymmetrically the original vanilla model treats replicas.

The corrections in $E_2$ and $E_3$ affect coefficients with repeated group indices. They do not affect any distinct-group coefficient. It would generally be incorrect to identify the entire cubic homogeneous part of $Q$ with $T$. The squarefree completion argument is needed precisely to recover the repeated-index coefficients of $T$ from the distinct-group coefficients when these approach the target tensor.

## Head-count consequence

If a separate quantitative argument proves that some finite $f_m$ has vanilla head complexity at least four, the pure upper construction above has exactly three heads. A two-head pure realization would imply a two-head vanilla realization by `vanillaComputable_two_of_pureRoPE`, a contradiction. The formal conditional statement is `ThreeHeadReplication.exact_three_of_upper_and_vanilla_lower`.

## Formal pure upper family

`PureRoPEReplication.replicatedAtom_eval` proves the exact mean-coordinate score identity for arbitrary positive replication count. `base_mass` and `base_sum` verify the fourteen-coordinate rational parameters. `pureRoPEComputable_three` gives the three-head upper bound for every real readout bias.

The declarations `explicitFunction_pure_three` and `explicitFunction_full_cube_sign` instantiate the count $m=2^{400000}$ and the negative rational bias used in the main separation note. The Lean function in this first module is defined by the biased score.

The separate module `Results/PureRoPEReplicationStrict.lean` formally proves the complete integer-lattice tie-removal argument. Its `scaled_cubic_integer` identifies the scaled unshifted cubic with an explicit integer expression on every input; `full_cube_strict` proves sign preservation and the uniform rational margin. The declarations `explicitUnshiftedFunction_pure_three`, `explicitUnshiftedFunction_eq`, and `explicitUnshiftedFunction_margin` give the actual unshifted classifier $[F\gt0]$ its pure three-head upper bound, its equality to the biased implementation, and its full-cube strict score margin. The exact token and query parameters are also checked. `explicitUnshiftedFunction_not_complement_invariant` proves that the all-zero and all-one inputs have different labels. These declarations use only the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

No lower bound for this explicit replicated function is asserted by these upper-bound modules. The averaging existence, degree, and sign-preservation steps are additionally formalized in the two mean-grid modules above. The complete finite Boolean lower bound in the main separation note remains a mathematical proof.
