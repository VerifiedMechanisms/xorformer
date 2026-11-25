# Local contact comparisons do not determine a feasible table

## Exact counterexample

A fixed affine basis with exactly two negative unit contacts has two different globally unit-feasible one-head truth tables whose entire affine coefficient comparison data agree. This remains true when every comparison against zero, both signed versions of the two nonzero contact levels is retained.

Use eight Boolean coordinates with most-significant-bit-first lexicographic vertex codes. The actual basis and its unit values are

$$ J=(166,151,202,178,18,218,185,188,200),\qquad g=(1,1,-1,-1,1,1,1,1,1). $$

Write $z(x)=(1,x_1,\ldots,x_8)$ and $A_k=z\cdot a_k$, $B_k=z\cdot b_k$. Take

$$ \begin{aligned} b_0&=(1,2,12,1,4,1,1,1,1),&a_0&=(1,-102,184,87,38,-67,53,-33,53),\cr b_1&=(1,1,11,1,1,1,1,1,1),&a_1&=(1,-79,151,71,31,-59,41,-29,41).\end{aligned} $$

Every denominator coefficient is strictly positive. The basis matrix has an integer inverse, and exact evaluation verifies

$$ A_k(J_j)=g_jB_k(J_j),\qquad |A_k(x)|\geq B_k(x)\gt0\quad\text{for every cube vertex}. $$

Thus both ratios are genuine admissible original heads and are globally unit feasible. They differ in sign precisely at vertex $15=(0,0,0,0,1,1,1,1)$, where their scores are $7/5$ and $-1$.

## Why all local coefficient comparisons agree

Normalize the affine difference by the second negative contact. Put

$$ C_k(x)=\frac{B_k(x)-A_k(x)}{2B_k(178)},\qquad r_k=\frac{B_k(202)}{B_k(178)},\qquad r_0=17/9,\qquad r_1=3. $$

The entire two-contact comparison pencil is

$$ C(r,x)=(2r+2)x_1-(4r+2)x_2-(2r+1)x_3-rx_4+2rx_5-(r+1)x_6+rx_7-(r+1)x_8. $$

Its constant coefficient is zero. For every $r\gt1$, each of its nine affine coefficients has the same signs relative to all five thresholds $0$, $r$, $1$, $-r$, and $-1$. This follows directly from the displayed coefficient formulas. In particular, both witnesses have identical data for the upward-contact comparisons and the downward-contact comparisons.

Nevertheless,

$$ C(r,00001111)=r-2. $$

Full unit feasibility makes the score positive exactly when $C\leq0$. The two ratios $17/9$ and $3$ therefore give different labels at this vertex while all the proposed local comparison data agree. The failing lemma is the implication from those coefficient comparison signs to the full Boolean sign pattern. A sum of individually controlled coordinate increments can cross an additional threshold.

The exact neighbor inequalities themselves remain valid: at a negative unit contact with $x_i=0$, the increment $c_i$ lies at most at the negative contact level or at least at twice the positive denominator slope. The kernel declarations `TwoMinorityBasisBranches.negative_contact_upward_dichotomy` and `negative_contact_downward_dichotomy` prove those inequalities. This example shows that they do not exhaust the full-cube constraints.

## Verification and scope

`Research/TwoMinorityNeighborObstruction.lean`, namespace `HeadComplexity.TwoMinorityNeighborObstruction`, checks original head admissibility, all full-cube unit gaps, the actual affine basis, exactly two negative contacts, the normalized ratios, the matching coefficient comparisons, and the differing labels. The exact certificate is also checked independently using Python fractions in `check_two_minority_neighbor_counterexample.py`; the root agent repeated the full-cube and five-threshold checks in `two-minority-comparison-root-check.json`.

The exploratory search first found the witness after 4989 eight-dimensional charts and 24783 linear programs. Floating output is not used as a proof premise. The saved exact integer coefficients and their complete cube checks replace that evidence.

This disproves a proposed linear-size set of local comparisons as a complete branch classifier. It does not disprove a polynomial bound on the number of feasible two-contact branches, a more global Boolean classification, or the unrestricted margin-repair theorem. A many-head lower bound would still need a joint contact-selection argument with arbitrary signed cancellation.
