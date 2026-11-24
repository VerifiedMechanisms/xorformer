# Two products, three vanilla heads

## Certified compiler

Let $R,A,B,C,D$ be arbitrary real affine forms on a finite Boolean cube. Suppose

$$ Q=R+AB+CD $$

has no zero value on the cube. Then the Boolean sign of $Q$ is computable by three heads in the unchanged vanilla xorformer model. There is no orientation restriction on the five input forms.

This is kernel-checked as `HeadComplexity.TwoProductsThreeHeads.computable_three` in `formalization/HeadComplexity/Results/TwoProductsThreeHeads.lean`. The same file proves `HeadComplexity.vanilla_three_of_positiveFraction_two` and `HeadComplexity.vanilla_three_of_retainedRoPE_two`. No original definitions are changed.

**Construction.** Choose an affine form $Z$ with coefficient $1+|B_i|+|D_i|$ at coordinate $i$ and constant term zero. Set

$$ V_0=Z+B,\qquad V_1=Z+D,\qquad V_2=Z,\qquad E_h=1-\varepsilon V_h. $$

Every $V_h$ has strictly positive coordinate coefficients. For sufficiently small positive $\varepsilon$, every $E_h$ is cube-positive and has strictly negative coordinate coefficients. Use the three fractions

$$ F_\varepsilon=\frac{A}{E_0}+\frac{C}{E_1}+\frac{-A-C+\varepsilon R}{E_2}. $$

Their exact cleared numerator is

$$ F_\varepsilon E_0E_1E_2=\varepsilon\left(AB E_1+CD E_0+R E_0E_1\right). $$

The parenthesized expression equals $Q+\varepsilon L+\varepsilon^2 M$, where

$$ L=-ABV_1-CDV_0-R(V_0+V_1),\qquad M=RV_0V_1. $$

Define the finite cube bounds

$$ \mu=\min_x|Q(x)|,\quad K=\max_{x,h}|V_h(x)|,\quad L_{\max}=\max_x|L(x)|,\quad M_{\max}=\max_x|M(x)|. $$

The following explicit choice is sufficient:

$$ \varepsilon=\min\left\lbrace\frac12,\frac{1}{2(1+K)},\frac{\mu}{2(1+L_{\max}+M_{\max})}\right\rbrace. $$

Indeed, $E_h(x)\gt 1/2$, and $|\varepsilon L(x)+\varepsilon^2M(x)|\lt\mu/2$. Consequently $F_\varepsilon$ has precisely the sign of $Q$ on every input. If the five forms are rational, this gives rational scalar fraction parameters. The Lean proof uses finite simultaneous continuity to select a positive parameter; the explicit bound here proves the same existence constructively.

**Architecture bridge.** Every constructed denominator is positive on the entire cube and has strictly uniform coordinate signs. The existing `RoPETwoHead.fraction_admissible` proves admissibility for arbitrary affine numerators. The existing `computableWithSharedHeadsN_iff_affineFractionComputable` then supplies the original shared-embedding vanilla architecture with three heads, unrestricted finite width, and real parameters. Thus the result concerns Boolean head count in that architecture, rather than just a formal rational score.

## Two positive fractions

For any score $S=c+N_0/D_0+N_1/D_1$ with cube-positive affine denominators, first decrease $c$ by a sufficiently small positive number. This preserves all Boolean labels and makes every score strictly nonzero. Clearing denominators then gives

$$ Q=\left(N_0+cD_0\right)D_1+N_1D_0. $$

The compiler applies with $R=0$. Therefore two arbitrary positive affine fractions, including two retained-RoPE heads, always admit a three-head vanilla Boolean realization. This statement allows all mixed denominator slopes and all degenerate numerator choices.

## Any three isolated positive vertices

Let $a,b,c$ be any three distinct vertices of a Boolean cube. The function positive exactly at these three vertices has a vanilla realization with at most three heads. This conclusion is a mathematical corollary of the kernel-checked compiler; the coordinate-selection and interpolation argument below is not separately Lean-formalized.

Choose a coordinate $p$ separating $a$ and $b$. The value of $c_p$ equals one of $a_p,b_p$; call that vertex $a$ after relabeling. Choose $q$ separating $a$ and $c$. Then $p\neq q$, and the three selected vertices occupy three distinct corners in their $(x_p,x_q)$ projection.

For every coordinate $i$, let $\lambda_i(x_p,x_q)$ be the unique affine function agreeing with coordinate $i$ of $a,b,c$ at those three corners. Its coefficients are integers, since the three-corner affine interpolation matrix has determinant $1$ or $-1$. Let $m$ be the missing corner, let $u,v$ denote the two literal indicators for disagreement with $m$, and put $R=2u+2v-1$. Thus $R$ is $-1$ at the missing corner, $1$ at its two neighbors, and $3$ at its opposite corner.

Consider the quadratic

$$ Q(x)=R(x_p,x_q)-4\sum_i\left(x_i-\lambda_i(x_p,x_q)\right)^2. $$

It is strictly positive at $a,b,c$. At any other Boolean vertex, either all residuals vanish, in which case the projection must be the missing corner and $Q=-1$, or a residual is a nonzero integer. In the latter case the sum of squares is at least one and $Q\leq 3-4=-1$. This verifies its signs on the full cube without enumerating the inputs.

Write $\lambda_i=\alpha_i+\beta_i x_p+\gamma_i x_q$. Reducing only the identities $x_i^2=x_i$, the quadratic becomes

$$ Q=R_0+x_p A_1+x_q A_2, $$

where all three forms on the right are affine and can be chosen as

$$ \begin{aligned}R_0&=R-4\sum_i\left[\alpha_i^2+(1-2\alpha_i)x_i+(2\alpha_i\beta_i+\beta_i^2)x_p+(2\alpha_i\gamma_i+\gamma_i^2)x_q\right],\cr A_1&=8\sum_i\beta_i x_i-8\left(\sum_i\beta_i\gamma_i\right)x_q,\cr A_2&=8\sum_i\gamma_i x_i.\end{aligned} $$

The compiler now applies. Its explicit parameter bound uses $\mu\geq 1$ here and yields rational scalar parameters determined by $a,b,c$.

## Scope of the obstruction

This rules out a pure-three versus vanilla-four separation obtained by declaring exactly three individual vertices positive. It does not rule out unions of three overlapping positive-dimensional Boolean faces, or general pure-three Boolean functions. No strict pure-RoPE separation is claimed.
