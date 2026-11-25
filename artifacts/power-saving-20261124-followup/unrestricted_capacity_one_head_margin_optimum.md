# Exact one-head relative-margin optimum on five bits

## Statement and status

Let $f(x)=+1$ exactly when the Hamming weight $|x|$ is at least two, on the full five-dimensional Boolean cube. In the original unrestricted model, among all one-head representations with arbitrary bias and either admissible denominator orientation, the largest relative margin is

$$ \gamma^{\ast}=\frac{5}{11+4\sqrt 6}. $$

This is an attained optimum with a strictly positive affine denominator. Thus a representation with normalized amplitude $K\gt 1$ need not admit any improvement at the same width. This statement does not rule out a constant-factor head-overhead repair, a tiny universal margin at the critical exponential widths, or a conditional result requiring genericity and stability under head duplication.

The complete optimum is now kernel checked against the original model in `formalization/HeadComplexity/Research/OneHeadOriginalMarginOptimum.lean`. The exact declaration `HeadComplexity.OneHeadOriginalMarginOptimum.hasRelativeMargin_iff` states that an original width-one representation with relative margin at least $\gamma$ exists if and only if $\gamma\leq\gamma^{\ast}$. The declarations `relativeMargin_le`, `exists_attaining`, and `exists_no_same_width_improvement` give the universal upper bound, an attained genuine-head witness, and the global no-improvement consequence. Their transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`. The proof was independently audited by the finite-margin agent.

## Arbitrary bias, signed numerators, and both orientations

Every original one-head score plus bias has the form $S=A/B$, where $A$ and $B$ are affine and $B$ is strictly positive on the whole cube. The bias is absorbed into $A$. Its original amplitude $D=|\beta|+\|\phi\| _\infty$ is at least $\|S\| _\infty$ by the triangle inequality. Rescale any correct representation so that its minimum signed score is one, and write $K=D$ after this rescaling.

The resulting inequalities are $B\leq A\leq KB$ on positive rows and $-KB\leq A\leq-B$ on negative rows. For fixed $K$, these inequalities are linear in the affine coefficients of $A,B$. Average the two coefficient vectors over all permutations of the five input coordinates. The target labels are permutation invariant, so all inequalities and strict positivity of the denominator survive. The averaged score has the form

$$ R(k)=\frac{a+bk}{c+dk},\qquad 0\leq k\leq5,\qquad c\gt0,\qquad c+5d\gt0. $$

This averaging is used only in a lower-bound relaxation. It is valid even for arbitrary cube-positive affine denominators, so in particular it includes both original coherent orientations and constant denominators. No independent coordinate complement is used. The slope $d$ is allowed to be negative. The Lean proof uses a smaller equivalent certificate: average the five singleton rows and the five cyclic adjacent-pair rows. Each coordinate occurs once and twice, respectively, so these affine sums give the same four inequalities. It never averages the values of ratios. These identities and the full-cube affine-ratio bound are checked in `OneHeadLayerAverages.lean`.

## Four rows force the optimum

The rows of weights zero, one, two, and five imply

$$ -Kc\leq a,\qquad a+b\leq-(c+d),\qquad c+2d\leq a+2b,\qquad a+5b\leq K(c+5d). $$

Subtracting the two middle inequalities gives $b\geq2c+3d$. Combining this with the first two gives $4d\leq(K-3)c$. Combining the first and last with the same lower bound on $b$ gives

$$ 0\leq(K-7)c+(5K-11)d. $$

Since $d\gt-c/5$, the bound $4d\leq(K-3)c$ implies $K\gt11/5$. Hence $5K-11\gt0$, and substituting the upper bound on $d$ into the preceding inequality is legitimate. It yields

$$ 0\leq5K^2-22K+5,\qquad K\geq K^{\ast}:=\frac{11+4\sqrt6}{5}. $$

The other quadratic root is excluded by $K\gt11/5$. This argument permits negative $d$ throughout; indeed $d\leq0$ in the displayed inequality already forces $K\geq7$.

The kernel declarations are `four_row_budget` and `four_row_budget_sharp`.

## A genuine head attains the bound

Set

$$ K=K^{\ast},\qquad d=\frac{K-3}{4},\qquad a=-K,\qquad b=2+3d. $$

Here $d\gt0$. The affine ratio $R(k)=(a+bk)/(1+dk)$ has values $-K,-1,+1,+K$ at $k=0,1,2,5$, respectively. Its cross determinant is $b-ad=b+Kd\gt0$, so it is strictly increasing wherever its denominator is positive. Thus all six Hamming layers have the required unit gap, and its full-cube supremum norm is exactly $K$.

The denominator $1+d\sum_i x_i$ has strictly positive intercept and slopes. Therefore `FracAtom.ofPositiveAffineRatio` constructs a genuine original head with this numerator and denominator. Taking bias zero makes the original amplitude exactly the score supremum $K$. The relative margin is exactly $1/K=\gamma^{\ast}$, matching the upper bound for every original one-head representation with arbitrary bias.

The scalar witness identities and monotonicity are the kernel declarations `sharp_parameters` and `ratio_strict_mono` in `OneHeadMarginOptimum.lean`. The helper `OneHeadLayerAverages.witness_layer_bounds` checks all six Hamming layers. The theorem `OneHeadOriginalMarginOptimum.exists_attaining` then constructs the genuine head, bounds its full-cube `atomSup`, proves strict signed labels, and combines its relative-margin lower bound with the universal upper bound. This completes the original-model quantification, including arbitrary replacement bias and both denominator orientations.

## Consequence for the capacity route

The first failing lemma is the proposed unconditional same-width escape: whenever an original representation has unit signed gap and amplitude greater than one, there is a width-preserving perturbation or replacement that decreases amplitude. The example above falsifies this lemma globally, including arbitrary admissible replacement denominators and bias.

It does not falsify the generic quadratic-feature theorem, whose hypotheses require stability after adding duplicate heads and sufficiently many generic denominators. Nor does it supply a badly conditioned truth table at the requested large widths: the exact optimum here is a fixed positive constant. A successful repair still needs a quantitative width budget and a substantially weaker target margin, or a capacity argument controlling the remaining nongeneric strata.

## Verification

The complete original wrapper builds successfully with 4,027 jobs. `OneHeadOriginalMarginOptimumAudit.lean` prints the transitive axioms of all six declarations; `one-head-original-margin-optimum-axioms.txt` contains only the standard three axioms. The independent scalar module built with 3,137 jobs and the finite-layer helper with 3,833 jobs. No definition of head admissibility, relative margin, or worst-case head complexity was changed.
