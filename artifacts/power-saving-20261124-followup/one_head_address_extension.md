# Unit contacts determine one-head address extensions

## Exact statement

Fix real functions $A,B$ on an address set $X$, with $B(x)\gt0$ for every $x$. The application has $X=\lbrace0,1\rbrace^d$ and positive affine $B$. Append $k$ Boolean coordinates $y$. Fix one address point $x_j$ and one sign $g_j\in\lbrace-1,+1\rbrace$ for every new coordinate. Consider affine extensions

$$ A_q(x,y)=A(x)+\sum_{j=1}^k\left(g_jq_j+g_jB(x_j)-A(x_j)\right)y_j,\qquad B_q(x,y)=B(x)+\sum_{j=1}^k q_jy_j,\qquad q_j\gt0. $$

These coefficients are precisely those forced by the actual unit observations $A_q(x_j,e_j)/B_q(x_j,e_j)=g_j$. Assume full unit feasibility: every pair $(x,y)$ has absolute score at least one.

**Theorem.** Every fully unit-feasible choice of positive $q$ has the same entire truth table. The signs are those of the canonical numerator

$$ A_0(x,y)=A(x)+\sum_{j=1}^k\left(g_jB(x_j)-A(x_j)\right)y_j. $$

The signs $g_j$ can be mixed. No restriction on the signs or magnitudes of the numerator coefficients is needed.

## Residual monotonicity

Let $f(x,y)$ be the sign of a fully unit-feasible extension. For any $0\leq q'_j\leq q_j$,

$$ f(x,y)A_{q'}(x,y)-B_{q'}(x,y)=f(x,y)A_q(x,y)-B_q(x,y)+\sum_{j=1}^k(q_j-q'_j)(1-f(x,y)g_j)y_j\geq0. $$

Every added term is nonnegative. Setting $q'=0$ gives $f(x,y)A_0(x,y)\geq B(x)\gt0$, so the entire truth table is determined by $A_0$. In particular two feasible choices cannot disagree at any point.

The zero-slope limit is an algebraic certificate. To keep all original heads admissible, choose any strictly positive smaller slopes instead. For positive affine $B$, both the old slopes and the new slopes then remain strictly positive. The displayed residual inequality preserves every label, the full unit gap, and the prescribed contacts. No inadmissible limiting head is used as a representation.

If the contact points and signs are not fixed but $A,B$ are fixed and $X$ has $M$ elements, there are at most $(2M)^k$ such fully unit-feasible extension tables. This counts the possible contact data; for each datum the theorem gives at most one table. When $M=2^d$ and $k=O(\log n)$, its logarithm is $O(n\log n)$.

## Why this does not close the unrestricted count

The theorem fixes the entire old affine numerator and denominator, not just the signs or real score values on the address face. An arbitrary actual sample basis need not consist of a basis on one address face and one singleton contact for each remaining coordinate. The open one-head counterexamples in `generic_one_head_basis_nonuniqueness.md` concern general actual bases and therefore do not contradict this special extension result.

For several heads, a total unit observation constrains the sum of the head values. It does not supply a signed unit contact for each head separately. The proof uses the nonnegative residual increment $(q_j-q'_j)(1-fg_j)y_j$ for one common ratio. Applying this argument separately to heads with arbitrary signed cancellation has no justification.

A useful unrestricted bridge would control all positive decompositions of a full real address score table, including degenerate fibers, with low-degree reconstruction charts. The present theorem does not provide that bridge. It removes the new denominator slopes only in the stated one-head contact geometry.

## Kernel-checked declarations

The file `formalization/HeadComplexity/Research/OneHeadAddressExtension.lean` proves:

- `HeadComplexity.OneHeadAddressExtension.contact_value`.

- `HeadComplexity.OneHeadAddressExtension.residual_mono`.

- `HeadComplexity.OneHeadAddressExtension.canonical_signed_gap`.

- `HeadComplexity.OneHeadAddressExtension.feasible_labels_unique`.

- `HeadComplexity.OneHeadAddressExtension.full_gap_preserved`.

The algebraic theorem permits any address set, so it applies to the whole Boolean address cube without sampling. The finite contact-count consequence is a written proof. No lower bound for unrestricted worst-case head complexity is claimed.
