# Minority contacts control one-head unit-basis extensions

## A positive fixed-basis theorem

Fix an affine basis of $n+1$ Boolean vertices, with prescribed unit values in $\lbrace-1,+1\rbrace$. Suppose $k$ contacts have the minority sign, and let $N=2^n$. Among positive affine denominators and affine numerators satisfying these contact equations and the full-cube unit gap, the number of possible full truth tables is at most

$$ \left(\frac{4eN}{k+1}\right)^{k+1},\qquad k+1\leq N. $$

If $k=1$, the entire full truth table is unique whenever a feasible representation exists. This conclusion permits every denominator to vary within the chart. It holds for all cube-positive affine denominators, so it covers both original coherent orientations. A bias in a one-head score can be absorbed into its affine numerator.

The fixed basis and its prescribed contact signs are essential. This is not an upper count over all choices of bases, and it does not control sums of several heads.

## Interpolation and the minority subspace

Assume the minority sign is negative, replacing the numerator and all labels by their negatives otherwise. Let $p_j$ be the basis points and $L_j$ their affine interpolation functions, characterized by $L_j(p_i)=1$ for $i=j$ and zero otherwise. Every affine form has its usual interpolation expansion on this basis. If $J_-$ is the set of negative contacts, the contact equations give

$$ A(x)=B(x)-2\sum_{j\in J_-}B(p_j)L_j(x). $$

Set $F=B-A$. It lies in the fixed $k$-dimensional span of the minority interpolation functions. Its coefficients are positive because $B(p_j)\gt0$.

The full unit-gap condition is $|A(x)|\geq B(x)\gt0$. If $F(x)\leq0$, then $A(x)\geq B(x)$, so the label is positive. If $F(x)\gt0$, then $A(x)\lt B(x)$, and the full unit gap forces $A(x)\leq-B(x)$, so the label is negative. Therefore

$$ f(x)=+1\quad\Longleftrightarrow\quad F(x)\leq0. $$

The same argument with the signs reversed uses the positive-contact subspace, giving the smaller of the two contact counts.

### One minority contact

When $J_-=\lbrace q\rbrace$, the formula becomes $F(x)=2B(q)L_q(x)$. Its positive scalar coefficient cannot change its sign pattern. Thus every feasible denominator gives the same full truth table, including at points where $L_q=0$.

This uniqueness is compatible with the separate one-minority balance obstruction: the fixed chart in `one_minority_balance_obstruction.md` has only one feasible table, yet every denominator in that branch has normalized constant at most $1/22$. Denominator imbalance and multiplicity of truth tables are different issues.

## Finite counting proof

Write $F(x)=\sum_{j=1}^k c_jL_j(x)$. For any fixed realized table, choose $\epsilon\gt0$ smaller than every positive value of $F$ on the finite cube. Then the polynomial comparison score

$$ \epsilon-\sum_{j=1}^k c_jL_j(x) $$

has exactly the required strict labels. It uses $k+1$ real parameters and has degree one in those parameters. The unconditional strict Warren theorem therefore gives the displayed bound. Allowing arbitrary real coefficients in this comparison class only enlarges the count.

## Kernel status

`HeadComplexity.MinorityContactCapacity.one_minority_unique` in `Research/MinorityContactCapacity.lean` proves uniqueness from the common scalar-factor identity, positive denominators, and full unit gaps. `unit_gap_sign_iff` proves the sign identity. `mem_comparison_of_unitFeasible` handles the finite strictification, and `card_unitFeasiblePatterns_le` proves the displayed finite count for an explicitly supplied $k$-function comparison space. The passage from an actual affine basis to its interpolation functions above is written linear algebra; no unproved interpolation premise is hidden in the kernel declarations.

The module builds successfully, and the transitive axiom logs are recorded alongside this note. Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` are used.

## Remaining obstruction

For balanced contact signs, $k$ can be proportional to $n$, leaving an exponent of order $n^2$. Moreover, separately choosing a basis for each head already costs order $n^2H$ in entropy. A useful unrestricted improvement would need a joint contact selection for the entire score and a bound on the remaining feasible extensions. The minority-space theorem supplies neither of those missing steps.
