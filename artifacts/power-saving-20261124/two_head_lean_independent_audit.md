# Independent audit of the two-head Boolean cancellation formalization

## Verdict and scope

I independently read `AffineBooleanZeroDivisors.lean` and `TwoHeadBooleanDegeneracy.lean`, then compiled the latter with `lake env lean HeadComplexity/Research/TwoHeadBooleanDegeneracy.lean`. The build succeeded. Every printed theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. No new axiom or `sorry` occurs in either file.

The formal result is an exact cancellation theorem for dimensions at least five. It does not prove the sharp dimension-four classification in the separate written note, and it does not assert any asymptotic head lower bound.

## Statements checked

`HeadComplexity.AffineBooleanZeroDivisors.support_card_le_two` states that if two affine functions have zero product at every Boolean input and one factor is not the zero affine function, then the other has at most two nonzero slopes. The proof extracts the constant, singleton, and pair coefficients. Three nonzero slopes in one factor force every coefficient of the other factor to vanish. The subsequent one-slope and two-slope declarations classify the surviving factors.

`HeadComplexity.TwoHeadBooleanDegeneracy.diagonal_support_card_le_four` concerns an identity $AC+DB=0$ on the Boolean cube. Its spatial coefficient matrix factors through a four-dimensional vector space. Since all off-diagonal entries vanish, at most four diagonal entries are nonzero. Consequently `exists_zero_diagonal` supplies a zero diagonal whenever $n\geq 5$.

At such an index $j$ with $b_j\neq 0$, `factor_at_zero_diagonal` defines $\kappa=a_j/b_j$ and $\ell=c_j/b_j$. The coefficient equations yield the affine identity $D+\kappa C=-\ell(A-\kappa B)$ and the Boolean zero-product identity below.

$$ (A-\kappa B)(C-\ell B)=0. $$

Finally, `denominator_difference_support_le_two` assumes positivity of both denominators at every cube input, nonzero slopes of $B$, and that $A$ is not a scalar multiple of $B$. It concludes that some positive $\ell$ makes $C-\ell B$ have at most two nonzero slopes. The nontriviality assumption supplies a vertex where the first factor is nonzero. At that vertex, the second factor vanishes, so denominator positivity proves $\ell\gt 0$. The support assertion then follows from the previously checked zero-divisor theorem.

The final theorem does not require slope coherence of $C$, and requires only nonzero slopes of $B$. Thus its assumptions cover any nonconstant coherent denominator chosen as $B$. When one denominator is constant and the other is not, an application can interchange the two summands first. This observation is a written bridge, not an additional Lean declaration.

## Limits

The theorem constrains exact two-head dependencies. A zero relation involving three or more denominators need not contain a nontrivial pair relation. Nothing in these declarations counts strict Boolean labels of arbitrary-width sums, establishes a margin repair, or shows that denominator configurations can be deformed into a pencil or collision while preserving labels.
