# Two minority contacts already permit two open branches

## Exact statement

A fixed actual affine basis with exactly two negative unit contacts and six positive unit contacts can support two different full Boolean truth tables, even when every denominator coefficient is strictly positive. Both feasible branches contain an open set of denominator parameters. They also have the same coefficient-sign pattern for the affine difference between denominator and numerator.

This strengthens the earlier nonuniqueness examples in a different direction: the one-minority uniqueness theorem is sharp as a uniqueness statement. It does not disprove a polynomial bound on the number of branches when there are two minority contacts.

## Certificate

Use seven Boolean coordinates, with vertex codes in lexicographic order from the most significant bit. The eight basis vertices and their unit values are

$$ J=(83,29,101,89,9,109,116,97),\qquad g=(1,1,-1,-1,1,1,1,1). $$

For $z(x)=(1,x_1,\ldots,x_7)$, let $B_k=z\cdot b_k$ and $A_k=z\cdot a_k$, where

$$ \begin{aligned} b_0&=(2,2,9,6,6,2,2,2),&a_0&=(-32,-68,113,40,40,-32,72,2),\cr b_1&=(2,2,11,2,2,2,2,2),&a_1&=(-36,-56,107,40,40,-36,60,2).\end{aligned} $$

Every denominator coefficient is positive. The original constructor `FracAtom.ofPositiveAffineRatio` therefore produces admissible heads, and exact evaluation gives

$$ A_k(J_j)=g_jB_k(J_j),\qquad |A_k(x)|\geq B_k(x)\gt0\quad\text{on the full cube}. $$

The augmented basis matrix has an integer inverse, recorded in `two-minority-branches-exact.json`; the Lean declaration `basis_affine_injective` checks the required independence directly. The two labels differ precisely at vertex codes $6$ and $7$. At code $6$ the scores are respectively $8/6$ and $-12/6$.

The affine differences have coefficient vectors

$$ b_0-a_0=(34,70,-104,-34,-34,34,-70,0),\qquad b_1-a_1=(38,58,-96,-38,-38,38,-58,0). $$

Thus merely fixing the coefficient-sign orthant of the comparison pencil does not determine its full feasible truth table.

## Open feasibility

Let $Z$ be the augmented basis matrix and $T=Z^{-1}\mathrm{diag}(g)Z$. For every denominator coefficient vector $b$, the numerator $Tb$ has exactly the prescribed unit basis values. There are twenty structural rows on which the signed gap is identically zero as a function of $b$. On all remaining rows, the exact signed residual at each displayed vector is at least two:

$$ f_k(x)z(x)\cdot Tb_k-z(x)\cdot b_k\geq2. $$

The twenty structural rows are listed in the exact certificate. Positivity of every denominator coefficient and strict positivity of the finitely many nonstructural residuals persist on an open neighborhood. Each neighborhood therefore contains only globally unit-feasible scores with the same full table as its center. Since the tables differ, these neighborhoods are disjoint.

## Kernel and computational status

The module `Research/TwoMinorityBasisBranches.lean`, namespace `HeadComplexity.TwoMinorityBasisBranches`, proves `basis_affine_injective`, `exactly_two_negative_contacts`, `same_difference_coefficient_signs`, `neighborhood_basis_values`, `neighborhood_signed_gap`, `label_disagreement`, and `two_open_feasible_branches`. The proof retains original admissibility through `atom` and `atom_eval`.

The exploratory search checked 100725 seven-dimensional basis charts and solved 466908 interval linear programs, with two as the largest recorded branch count. Those floating searches are not used as theorem premises. `check_two_minority_branches.py` checks the saved witness independently with integers, and Lean checks the finite cube inequalities and the openness argument. Search outputs, exact certificates, build logs, and transitive axiom audits are saved alongside this note.

## Failed amplification and remaining question

Writing $C=B-A$, a two-minority chart has $C$ in a fixed two-dimensional span. After positive normalization, its candidate labels are determined by a one-parameter pencil $rL_1+L_2$, with $r\gt0$. Generic arrangement counting still permits a number of branches depending on $N$.

One attempted amplification appends a coordinate $y$ and one new positive unit contact at $(x_0,1)$, retaining the two negative contacts on $y=0$. The resulting difference is exactly

$$ C'(x,y)=C(x)-C(x_0)y. $$

This introduces additional candidate threshold ratios, but full-cube unit-gap feasibility must be checked anew. Floating scans over all 128 anchors in dimension eight, followed by all 256 anchors for the selected nine-dimensional extension, found no increase beyond two feasible tables. These are finite negative observations, not an obstruction to another extension or a proof that two is the general maximum.

A particular cloning extension fails exactly. Scale numerator and denominator together so that $2B(89)=1$. In this normalization the comparison pencil is

$$ C(r,x)=r(1+x_1-2x_2-x_3-x_4+x_5-x_6)+(x_1-x_2-x_6). $$

The positive contact anchored at code $25$ gives $C^{\prime}=C+r y$, cloning the coefficient of $x_5$. At the negative contact $q=101$, the comparison equals $r\gt0$. Adding the missing coordinate $x_3$ and the new coordinate $y$ leaves its comparison equal to $r$, because their increments are $-r$ and $r$. It strictly increases the denominator, because both slopes must remain positive. Full feasibility at that larger vertex would therefore require

$$ r\geq2B^{\prime}(x)\gt2B^{\prime}(q)=r, $$

which is impossible. The general two-point inequality is kernel checked as `negative_contact_difference_strict` and `equal_difference_impossible`; the substitution of this particular extended pencil is written algebra. Thus this cloning construction cannot amplify the branch count. The obstruction concerns a strict coordinatewise superset on the same positive comparison level, not arbitrary new head directions or arbitrary basis extensions.

A bound independent of $N$, or an exponential family of feasible branches with only two minority contacts, remains open. In either case, an unrestricted many-head lower bound would still require a joint basis-selection argument and control of signed cancellation between heads.
