# Positive reciprocal geometry and the signed-cancellation obstruction

## Positive reciprocal moment coordinates

Let $Z$ be a finite real row matrix, let $B_x(b)=z_x\cdot b$, and restrict parameters to the convex domain where every $B_x(b)$ is positive. For positive observation weights $w_x$, define

$$ \Gamma_w(b)=\sum_x\frac{w_xz_x}{B_x(b)}. $$

The exact identity

$$ (b-c)\cdot\bigl(\Gamma_w(b)-\Gamma_w(c)\bigr)=-\sum_x\frac{w_x\bigl(B_x(b)-B_x(c)\bigr)^2}{B_x(b)B_x(c)} $$

shows that equal gradients force equal evaluation vectors. If the rows span the parameter space, the parameters themselves agree. This conclusion has no algebraic-degree loss.

`PositiveReciprocalGradient.monotonicity_identity`, `evaluation_eq_of_gradient_eq`, and `injective_gradient_on_positive_domain` kernel check this argument for arbitrary finite row and parameter index sets. Positivity of every denominator and every observation weight is explicit in the theorem hypotheses.

This is the elementary diagonal version of the likelihood uniqueness mechanism in [Sturmfels and Uhler, *Multivariate Gaussians, semidefinite matrix completion, and convex algebraic geometry*](https://www.ism.ac.jp/editsec/aism/pdf/062_4_0603.pdf), especially Sections 1 and 3. Their positive reciprocal projection can be unique despite a large complex algebraic degree. The theorem above is proved directly in Lean and does not assume that literature result.

## A full signed gradient is not injective

Use all four augmented rows of the two-dimensional Boolean cube in the order $(0,0),(1,0),(0,1),(1,1)$. Set

$$ w=(2,-6,-12,20),\qquad b=(1,1,2),\qquad c=(2,1,2). $$

Every coefficient of both denominator vectors is strictly positive, and the four denominator evaluations are respectively $(1,2,3,4)$ and $(2,3,4,5)$. Nevertheless

$$ \Gamma_w(b)=\Gamma_w(c)=(0,2,1),\qquad b\neq c. $$

The declarations `SignedCounterexample.parameters_pos`, `evaluations_pos`, `gradient_values`, and `parameters_ne` kernel check this example. Unlike an arbitrary dual hyperplane, the observation map here is precisely the complete reciprocal gradient associated to the actual affine rows. The failed hypothesis is positivity of the observation weights.

This does not prove that these exact signed weights occur in a valid global margin optimality certificate. It only rules out discarding that hypothesis in the positive-gradient uniqueness theorem.

## Where signs enter a proposed optimization certificate

For an original score $S=b+\sum_h A_h/B_h$ and constraints $f_xS_x\geq1$, nonnegative Lagrange multipliers $\lambda_x$ contribute to the derivative with respect to a denominator parameter the terms

$$ -\sum_x\lambda_x f_x A_h(x)\frac{z_x}{B_h(x)^2}. $$

The coefficients $\lambda_xf_xA_h(x)$ need not be positive. Full feasibility controls the sum over heads, not each signed head contribution. Numerator stationarity gives additional weighted linear identities, but no implication converting this system to an injective positive reciprocal-gradient problem has been proved.

The precise remaining lemma for this route would supply a canonical globally feasible representation and a reconstruction certificate whose reciprocal critical equations have positive observation weights, with only $O(nH)$ selected actual rows and $\exp(O(nH\log n))$ additional choices. The positive-gradient theorem would then remove the branch index for that certificate. The existence and sufficiency of such a certificate remain open.

## A concrete log-barrier failure

A natural attempted objective is the negative logarithm of the signed score, possibly stabilized by logarithms of the positive denominators. Even three heads disprove uniform convexity of this objective.

On one Boolean bit, take strictly positive affine denominators

$$ B_1(x)=1+(1+t)x,\qquad B_2(x)=1+(1-t)x,\qquad B_3(x)=1+x,\qquad |t|\lt1, $$

and constant numerators $1,1,-2+\varepsilon$, where $0\lt\varepsilon\lt2$. Each ratio is an admissible original head by `FracAtom.ofPositiveAffineRatio`. The full score is positive at both Boolean points. At the origin it equals $\varepsilon$. At the other point,

$$ S_t(1)=\frac{1}{2+t}+\frac{1}{2-t}-\frac{2-\varepsilon}{2}=\frac{4\varepsilon+(2-\varepsilon)t^2}{2(4-t^2)}. $$

Consequently

$$ S_0(1)=\frac{\varepsilon}{2},\qquad S'_0(1)=0,\qquad S''_0(1)=\frac12,\qquad \left.\frac{d^2}{dt^2}\bigl(-\log S_t(1)\bigr)\right|_{t=0}=-\frac1\varepsilon. $$

The denominator barrier $-\sum_h\log B_h(1)$ has second derivative $1/2$ at zero. Thus adding any fixed multiple of this barrier cannot make the label-barrier objective convex uniformly as $\varepsilon$ tends to zero. The denominator intercepts stay normalized to one, so this failure is not caused by an unremoved denominator scaling.

For $\varepsilon=1$, clearing denominators gives $4+t^2$ at the nonzero Boolean point. Its logarithm also has a strict local minimum at zero, disproving concavity of the cleared-score log barrier directly.

These derivative calculations and their original-model construction are written proofs. They are not exported Lean theorems. The truth table is constant and easy, so the example does not obstruct a global truth-table-preserving repair or prove a capacity lower bound. It rules out the proposed blanket convexity argument on the full positive parameter cell.

## The Boolean split and Cauchy matrices

Splitting the input into two bit blocks writes each head matrix as

$$ M_h(x,y)=\frac{u_h(x)+v_h(y)}{r_h(x)+c_h(y)}. $$

Its Sylvester displacement is rank at most two:

$$ \mathrm{diag}(r_h)M_h+M_h\mathrm{diag}(c_h)=u_h\mathbf1^{\top}+\mathbf1v_h^{\top}. $$

The displacement operators differ between heads. Multiplying the commuting row-column operators produces a common annihilator but a rank bound exponential in $H$, which is vacuous at the requested widths. A single original reciprocal head already gives a full-rank Cauchy matrix when the two blocks use binary-address denominator weights, so ordinary matrix rank is not an additive head-count invariant.

Relaxing the row and column generators to arbitrary arrays also loses the necessary scale: a balanced split introduces order $H\sqrt N$ parameters, already more than $N$ at the critical widths. A useful sign-specific matrix theorem must retain their Boolean subset-sum dependence. No such theorem was obtained in this attempt.

The Cauchy discussion is a written assessment of this approach, not a new unrestricted lower bound.
