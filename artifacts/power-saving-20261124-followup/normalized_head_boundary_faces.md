# The closure of a normalized head has finitely many face charts

## Statement

Consider original admissible heads with full-cube supremum norm at most one. Their pointwise closure on the Boolean cube has a description by at most

$$ 2(n+1)^{n+1} $$

discrete charts, each using at most $2(n+1)$ real coefficients. Each chart consists of an ordered list of disjoint coordinate groups, weighted averages on successive anchored face differences, and a terminal affine ratio with positive constant denominator on the last face.

The factor two chooses the original denominator orientation. This is a written exact characterization of the closure, including the converse approximation construction. It is not presently a Lean declaration. It controls the leading head limits but not the strict labels hidden by cancellation of those limits.

## Normalization and a coefficient bound

After reflecting all coordinates if necessary, every original head has the form

$$ \phi(x)=\frac{a_0+\sum_{i=1}^n a_i x_i}{b_0+\sum_{i=1}^n b_i x_i},\qquad b_0\gt0,\qquad b_i\geq0. $$

Positive simultaneous scaling of numerator and denominator makes $\sum_{i=0}^{n}b_i=1$. The norm assumption gives $|A(x)|\leq B(x)$ on the entire cube. At the zero and singleton vertices it implies

$$ |a_0|\leq b_0,\qquad |a_i|\leq|a_0+a_i|+|a_0|\leq b_i+2b_0. $$

Thus every numerator coefficient is bounded after this denominator normalization. No restriction on its sign is imposed.

## Construction of the limiting chart

Take any sequence of normalized heads. Pass to a subsequence on which the orientation is fixed. At the first stage, extract convergent denominator and numerator coefficients. The denominator limits lie in the nonnegative simplex, so at least one is positive.

If the limiting constant coefficient is positive, the limiting head is an affine ratio with positive constant denominator on the whole cube. Some slope coefficients may vanish. The numerator coefficients in those directions need not vanish, which is why the terminal chart permits arbitrary numerator slopes subject to its norm bound.

Otherwise let $I_1$ be the nonempty set of coordinate indices whose denominator limits are positive. Outside the anchored face where every coordinate in $I_1$ is zero, the pointwise limit is

$$ \frac{\sum_{i\in I_1}\alpha_i x_i}{\sum_{i\in I_1}\beta_i x_i},\qquad \beta_i\gt0,\qquad |\alpha_i|\leq\beta_i. $$

Indeed the constant numerator limit vanishes, and the coefficient bound forces every numerator coefficient outside $I_1$ to vanish. This expression is a weighted average of the numbers $\alpha_i/\beta_i\in[-1,1]$ over the active coordinates in the group. It is independent of later coordinates.

On the remaining anchored face, discard the indices in $I_1$. Divide all remaining numerator and denominator coefficients by the sum of the remaining denominator coefficients. This sum is strictly positive at every finite stage because it still includes $b_0$. The rescaled denominator coefficients again lie in a simplex. The same coefficient inequalities bound the rescaled numerator coefficients, since the constant coefficient remains among them.

Extract another convergent subsequence and repeat. Whenever the limiting constant coefficient is zero, at least one additional coordinate has positive limiting denominator coefficient and is removed into the next nonempty group. After at most $n$ removals, the constant coefficient must appear with positive limit. Only finitely many subsequence extractions are needed.

The result is an ordered list of disjoint nonempty groups $I_1,\ldots,I_r$ and a residual coordinate set $J$. An input is evaluated by the first group containing an active coordinate. If there is no such group, it lies on the final anchored face and is evaluated by a terminal ratio

$$ \frac{\alpha_0+\sum_{i\in J}\alpha_i x_i}{\beta_0+\sum_{i\in J}\beta_i x_i},\qquad \beta_0\gt0,\qquad \beta_i\geq0. $$

The terminal ratio has absolute value at most one throughout its face, by passing the original pointwise inequalities to the limit. Its numerator is otherwise arbitrary. Every nonterminal coefficient pair belongs to its own group, and the terminal pairs belong to the residual variables and constant. Hence there are at most $2(n+1)$ real coefficients in total.

## Every such chart is a limit of admissible heads

Conversely, take any chart with the displayed coefficient conditions and a terminal ratio bounded in absolute value by one. Let $A_j,B_j$ be its homogeneous affine numerator and denominator on group $I_j$, and let $A_{\ast},B_{\ast}$ be the terminal affine forms on $J$. Set

$$ A_t=\sum_{j=1}^{r}t^{j-1}A_j+t^rA_{\ast},\qquad B_t=\sum_{j=1}^{r}t^{j-1}B_j+t^rB_{\ast}+t^{r+1}\sum_{i=1}^n x_i. $$

For every $t\gt0$, the denominator constant and every slope coefficient are strictly positive. The numerator is affine with arbitrary signed coefficients. Therefore $A_t/B_t$ is an original admissible head by `FracAtom.ofPositiveAffineRatio_eval`.

Every nonterminal group satisfies $|A_j(x)|\leq B_j(x)$. The terminal norm assumption gives $|A_{\ast}(x)|\leq B_{\ast}(x)$ on all residual inputs. The triangle inequality therefore yields $|A_t(x)|\leq B_t(x)$ everywhere, so the full-cube norm is at most one.

At an input whose first active group is $I_j$, divide numerator and denominator by $t^{j-1}$ and pass to the limit. This gives that group's weighted-average ratio. If all groups are inactive, division by $t^r$ gives the terminal ratio. Thus the chart is exactly the pointwise limit of the constructed original heads.

## Discrete chart count and finite sums

A chart is specified by assigning a layer number in $\lbrace0,\ldots,n\rbrace$ to each coordinate and to the constant coefficient. The constant's layer is terminal, all earlier used layers are ordered, and all residual coordinates can be assigned to that terminal layer. Ignoring these constraints gives at most $(n+1)^{n+1}$ assignments. Including the two global orientations gives the stated upper bound.

For a normalized score with $H$ heads and bias, the amplitude condition bounds the bias and every head norm. Simultaneous subsequence extraction therefore gives a limiting bias and one such chart per head. The number of discrete leading-limit choices is at most

$$ \left(2(n+1)^{n+1}\right)^H, $$

whose logarithm is of order $nH\log n$. The limiting score is described by at most $1+2(n+1)H$ real coefficients. This statement includes arbitrary signed cancellation between heads, because it describes each summand before adding it. The full amplitude is continuous under pointwise convergence on the finite cube.

## What is still missing

If the limiting score is strict, its labels are already determined by these leading charts. If some score coordinates vanish, later terms can determine their labels. If the complete leading score cancels, all labels can remain undecided.

The [mixed-difference construction](weak_limit_layer_obstruction.md) shows that even uniformly interior denominators can have many successive normalized orders of vanishing, with more than $nH\log n$ layers at the logarithmic fallback width. That construction has only one truth table, so it also shows why layer multiplicity alone is the wrong entropy measure.

To reach an unrestricted capacity bound, one needs a count for the jointly constrained signs of all cancellation refinements. The finite face-chart count proved here is not such a count and cannot be multiplied independently over those refinements.
