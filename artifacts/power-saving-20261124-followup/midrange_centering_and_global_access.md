# Midrange centering and the global margin access problem

## Kernel-checked exact repair

Let $S=b+\sum_{h=1}^H\phi_h$ be a score of genuine original-model heads. All extrema and norms below are taken over the entire Boolean cube. Define

$$ a_h=\min_x\phi_h(x),\qquad z_h=\max_x\phi_h(x),\qquad m_h=\frac{a_h+z_h}{2},\qquad r_h=\frac{z_h-a_h}{2}. $$

Set $\psi_h=\phi_h-m_h$ and $b'=b+\sum_hm_h$. Every $\psi_h$ is still one admissible head. In the original `FracAtom` parameters, subtracting a constant $m$ replaces $\eta$ by $\eta-m\gamma$ and every $m_i$ by $m_i-m$, leaving all positive attention parameters unchanged.

The complete score table is unchanged, the extrema of each new head are $-r_h$ and $r_h$, and

$$ |b'|+\sum_h\|\psi_h\|_\infty\leq|b|+\sum_h\|\phi_h\|_\infty. $$

Indeed, $|m_h|+r_h=\max(|a_h|,|z_h|)=\|\phi_h\|_\infty$, and the triangle inequality applies to the new bias. Therefore relative margin cannot decrease, at exactly the same width and with the same truth table.

This is kernel checked in [MidrangeMarginCentering.lean](../../formalization/HeadComplexity/Research/MidrangeMarginCentering.lean). The main declarations are `centered_score`, `centered_amplitude_le`, `centered_relativeMargin_ge`, and `exists_centered_certificate`, in namespace `HeadComplexity.MidrangeMarginCentering`. The last declaration includes balanced full-cube extrema for every head. It assumes a genuine relative-margin certificate, not a fixed denominator dictionary. No quantitative lower bound on the resulting margin is asserted.

## Why the constant gauge must be removed

Without centering, every original score can be made into a misleading collision family without moving any denominator. Write $\phi_h=A_h/B_h$ and choose arbitrary constants $c_h$. Then

$$ \phi_h(t)=c_h+t\phi_h=\frac{c_hB_h+tA_h}{B_h},\qquad b(t)=-\sum_hc_h+tb,\qquad b(t)+\sum_h\phi_h(t)=tS. $$

All heads remain admissible. For positive $t$, every label is unchanged, while the displayed representation can have arbitrarily small relative margin. Its first nonzero tangent is the entire original model with arbitrary separated denominators. Thus a theorem about one cancelling family cannot identify a low-entropy exceptional class. Centering removes this particular degeneracy exactly.

## Compact closure of individual centered heads

The following description is a written proof, not a Lean declaration. It concerns limits of individual normalized heads and does not establish a global margin repair.

After selecting one denominator orientation and, if necessary, reflecting all input coordinates for that head, write a sequence of heads as $A_k/B_k$, where $B_k=b_{k,0}+\sum_i b_{k,i}x_i$ has nonnegative slopes and positive intercept. Normalize $b_{k,0}+\sum_i b_{k,i}=1$, and assume the output norm is at most one. Then

$$ |A_k(x)|\leq B_k(x)\leq1\quad\text{at every Boolean vertex}. $$

In particular, the affine numerator coefficients are bounded: the intercept has absolute value at most one, and each slope has absolute value at most two. Passing to a subsequence gives coefficientwise limits $A,B$.

If the limiting intercept is positive, every denominator stays bounded away from zero, and the output limit is the ordinary affine ratio $A/B$. Constant-denominator limits are allowed here even when they are only limits of original heads.

If the limiting intercept is zero, let $J$ be the nonempty set of coordinates with positive limiting denominator coefficient. On the face where all coordinates in $J$ vanish, the limiting numerator also vanishes. Hence its intercept and every numerator coefficient outside $J$ are zero. Outside that face the limiting output is

$$ \frac{\sum_{i\in J}a_i x_i}{\sum_{i\in J}b_i x_i},\qquad b_i\gt0,\qquad |a_i|\leq b_i. $$

It is independent of every other coordinate. On the exceptional face, restrict the original sequence and renormalize the remaining denominator coefficient mass. The same argument applies on a strictly smaller cube. Repetition stops after at most $n$ proper faces.

Thus a limit is described by an ordered partition of some coordinates into nonempty priority blocks, followed by an ordinary positive-intercept affine ratio on the remaining coordinates. Each nonterminal block contributes its ratio only when every preceding block is zero and at least one bit in that block is one. The number of levels is at most $n+1$. The continuous coefficient count is $O(n)$ because the blocks use disjoint coordinate sets; the discrete chart count is at most $2^{O(n\log n)}$. Reflecting coordinates gives the other denominator orientation. Centering and norm bounds pass to the output limit.

This also follows at the level of existence from compactness of the finite output cube $[-1,1]^N$. The recursive description identifies which individual boundary values can occur, rather than assigning arbitrary independent values on a zero-denominator face.

## The first unresolved global step

After centering and normalizing the total amplitude, write the score as a bias plus a nonnegative weighted sum of centered norm-one heads, with the absolute bias plus the weight sum at most one. The closure of this finite-width family in output space is compact. Consequently the supremal signed margin is attained in that closure. Every strict closure certificate can be approximated by genuine heads at the same width, preserving all labels and any strictly smaller margin.

This gives existence of a global optimum in the compactified family, but it does not give a useful lower bound on its value. In particular, small globally optimal margin does not by compactness alone force a collision of several head directions. The individual boundary hierarchy above also contains the ordinary interior one-block class. Clearing the selected positive denominator at each Boolean row still has degree proportional to the number of heads and retains the original counting obstruction.

One precise missing access statement is a quantitative escape or counting theorem for complete label cells: if every centered representation of a truth table at the allowed comparison width has margin below the threshold, then either the table has a favorable large-cluster representation or the entire collection of such tables has small cardinality. A small active minor in an optimized fixed-denominator problem is insufficient. An open semialgebraic label cell may lie in a thin tube near a rank-drop locus while its closure never meets that locus. Excluding this behavior here requires a property of the original Boolean evaluation map, not a generic compactness or stationarity argument.
