# Global Numerator Norm Obstructions

## Scope

The normalized score is

$$ S(x)=1+\sum_{h=1}^H\frac{u_h\cdot x}{1+b_h\cdot x}. $$

This note gives two complete counterexamples to proposed optimization shortcuts. The first makes every nontrivial ordinary Lagrangian dual functional unbounded below. The second gives a feasible two-head unit-margin problem whose numerator-norm infimum is zero and is not attained. Both constructions use admissible coherent slopes and literal fractional attention atoms. Neither proves the requested asymptotic lower bound for worst-case head complexity.

## A boundary escape

Identify cube vertices with subsets of $[n]$. Write $a(x)$ for arbitrary real coefficients, not all zero away from the empty set.

### Theorem 1. Unbounded functional with bounded numerator norm

For every real $R$ there are normalized coefficients $u,b$ satisfying

$$ b_i\lt0,\qquad \sum_i(-b_i)\lt1,\qquad \sum_i u_i^2\leq1,\qquad \sum_{x\subseteq[n]}a(x)\frac{u\cdot x}{1+b\cdot x}\gt R. $$

**Proof.** Choose a nonempty inclusion-maximal set $s$ with $a(s)\neq0$. Choose $i\in s$ and put $d=\mathrm{sgn}(a(s))$. For $t\gt0$ set

$$ w_j=\begin{cases}1&j\in s,\cr t&j\notin s,\end{cases}\qquad D_t(x)=t+\sum_{j\notin x}w_j,\qquad c_t=t+\sum_jw_j. $$

All these denominators are positive. If $x$ does not contain $s$, at least one weight equal to one occurs in the denominator, so $D_t(x)\geq1$. If $x$ properly contains $s$, maximality gives $a(x)=0$. At the selected vertex,

$$ D_t(s)=t(1+n-|s|)\leq t(n+1). $$

Let $L=\sum_x|a(x)|$. The preceding facts give

$$ \sum_x a(x)\frac{d\mathbf1_{i\in x}}{D_t(x)}\geq\frac{|a(s)|}{t(n+1)}-L. $$

Replace $R$ by $R_+=\max(R,0)$ and choose

$$ t=\frac{|a(s)|}{(n+1)(R_++L+1)}. $$

The functional is then at least $R_++1$. Normalize by

$$ b_j=-\frac{w_j}{c_t},\qquad u_j=\frac{d}{c_t}\mathbf1_{j=i}. $$

The normalized ratio equals the displayed ratio with denominator $D_t$. Every slope is negative and

$$ \sum_j(-b_j)=\frac{\sum_jw_j}{t+\sum_jw_j}\lt1. $$

Since $s$ is nonempty, $c_t\geq1$, whence the squared numerator norm is $1/c_t^2\leq1$. This proves the theorem. $\blacksquare$

### Corollary 2. The ordinary norm dual is trivial

Fix $H\geq1$ and a label table $y(x)\in\lbrace-1,1\rbrace$ with $y(0)=1$. Consider minimization of $\frac12\sum_{h,i}u_{h,i}^2$ under all constraints $y(x)S(x)\geq1$. For nonnegative constraint multipliers $\lambda(x)$, the Lagrangian is

$$ \mathcal L=\frac12\sum_{h,i}u_{h,i}^2+\sum_x\lambda(x)(1-y(x))-\sum_{h,x}\lambda(x)y(x)\frac{u_h\cdot x}{1+b_h\cdot x}. $$

If any multiplier away from the origin is positive, apply Theorem 1 with $a(x)=\lambda(x)y(x)$. Keep one varying head and set the other numerators to zero. Its norm remains bounded and its negative functional tends to negative infinity. Thus $\inf\mathcal L=-\infty$.

If the multipliers are supported only at the origin, the constant term vanishes, all head numerators vanish there, and $\inf\mathcal L=0$. Consequently the dual supremum is zero. This statement concerns the ordinary global Lagrangian dual; it does not exclude local first-order multiplier certificates such as the separately certified [strict local minimum](unit-margin-strict-minimum.md).

## A feasible infimum without a minimizer

### Theorem 3. Two heads with arbitrarily small norm

Let $n\geq2$. Label only the all-ones vertex negative and all other vertices positive. For every $\eta\gt0$ there is an admissible two-head representation with origin score one, signed margin at least one at every cube vertex, and squared normalized numerator norm less than $\eta$. No representation with zero squared numerator norm satisfies these margins.

**Proof.** Write $k=|x|$ and take $t\gt0$ with $4tn\leq1$. Define

$$ S_t(k)=1+\frac{4tk}{1+tk}-\frac{2tk}{t+n-k}. $$

For $k\lt n$, the second denominator is at least one and the first is at most two. Therefore

$$ \frac{4tk}{1+tk}\geq2tk\geq\frac{2tk}{t+n-k},\qquad S_t(k)\geq1. $$

At the all-ones vertex,

$$ S_t(n)=1+\frac{4tn}{1+tn}-2n\leq2-2n\leq-2. $$

The normalized coefficients of the two heads are

$$ u_{0,i}=4t,\qquad b_{0,i}=t,\qquad u_{1,i}=-\frac{2t}{n+t},\qquad b_{1,i}=-\frac1{n+t}. $$

The first head has strictly positive slopes. The second has strictly negative slopes and their absolute sum is $n/(n+t)\lt1$. Thus both heads are admissible. Their squared numerator norm satisfies

$$ \sum_{h,i}u_{h,i}^2=16nt^2+\frac{4nt^2}{(n+t)^2}\leq20nt^2. $$

For an explicit choice valid for every $\eta\gt0$, take

$$ t=\min\left(\frac1{8n},\frac{\eta}{40n+1}\right). $$

Then $0\lt t\leq1$, $4tn\leq1$, and $20nt^2\leq20nt\lt\eta$. A zero squared norm forces every numerator coefficient to be zero, making the score identically one and violating the negative label. Thus the feasible norm infimum is zero and is not attained. $\blacksquare$

## Verification and limitations

`formalization/HeadComplexity/Atoms/NegativePoleEscape.lean` proves Theorem 1 as `HeadComplexity.NegativePoleEscape.unbounded_normalized_functional`, constructs the actual fractional atom in `unbounded_atom_functional`, and proves the one-head arbitrary-constant Lagrangian conclusion in `lagrangian_unbounded_below`. Corollary 2 is the written finite-head deduction above.

`formalization/HeadComplexity/Atoms/VanishingNumeratorNorm.lean` proves `arbitrarily_small_norm`, the literal fractional-atom identity `atoms_score`, and `no_numerator_norm_minimum`. The last statement produces a strictly better admissible two-head representation for every feasible candidate, without requiring the candidate itself to have any restricted slope pattern.

All principal declarations pass the Lean kernel and use only `propext`, `Classical.choice`, and `Quot.sound`. The model and its complexity definitions are unchanged. These results block unconditional norm attainment and a nontrivial ordinary norm-duality certificate. They do not count arbitrary sign representations, and they do not establish any improvement over the manuscript's worst-case counting lower bound.
