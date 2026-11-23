# A sign-preserving spike with vanishing normalized energy

## Statement

Keep the manuscript's architecture, arbitrary real parameters, and unrestricted embedding dimensions. Let a Boolean function on $n\geq1$ inputs have a strict representation with $H$ heads. In the coherent denominator charts defined below, for every $\eta\gt0$ it has a strict representation with $H+1$ heads whose normalized independent-block denominator energy is less than $\eta$.

This is an obstruction to using the infimum of that energy as a head-count invariant. It is not a Boolean head-count lower bound. The original unbounded improvement over the counting bound and the stronger matching-order target remain open in this run.

## Definitions

Write $X=\lbrace0,1\rbrace^n$, $N=2^n$, and

$$ S(x)=c+\sum_{h=1}^{H}\frac{A_h(x)}{1+b_h\cdot z_h(x)},\qquad b_h\geq0. $$

Here $A_h$ is affine, and each $z_h(x)$ is either $x$ or its coordinatewise complement. Normalizing each head denominator at its smaller corner gives this presentation for either coherent orientation. A constant denominator has $b_h=0$. All original coefficients, signs, and orientations can depend on the target. If desired, continuity on the finite cube allows the constant-denominator heads to be perturbed to nonconstant admissible heads before the construction, preserving strict signs and head count.

For a nonnegative slope vector $b$, define

$$ E_b(v)=\sum_i b_i v_i^2+\left(\sum_i b_i v_i\right)^2. $$

For a nonzero score table $T$, let $G=\sum_x T(x)^2$. When the numerator coefficients and the other denominator blocks are held fixed, put $g_h(x)=\nabla_{b_h}T(x)$. The energy of the normalized table $U=T/\sqrt G$ is

$$ V(T)=\sum_h\sum_x E_{b_h}\bigl(\nabla_{b_h}U(x)\bigr)=\sum_h\frac{G\sum_x E_{b_h}(g_h(x))-E_{b_h}\bigl(\sum_x T(x)g_h(x)\bigr)}{G^2}. $$

The equality follows by differentiating $U$ and expanding the quadratic form. It uses independent slope blocks, including when different heads happen to have the same denominator. It does not differentiate along a tied one-dimensional family of parameters.

## Proof

### Lemma 1. Normalized energy bound

For every nonnegative $b$ and finite tables $T,g$,

$$ 0\leq E_b\left(\sum_x T(x)g(x)\right)\leq G\sum_x E_b(g(x)). $$

**Proof.** Apply the finite Cauchy-Schwarz inequality separately to each coordinate of $g$, multiply by the corresponding nonnegative coefficient $b_i$, and sum. Apply it once more to the scalar table $\sum_i b_i g_i(x)$. Adding the inequalities gives the assertion. Thus each block contribution to $V$ is nonnegative and at most its unnormalized energy divided by $G$. In particular, if $G\geq1$, it is at most its unnormalized energy. $\blacksquare$

### Lemma 2. One admissible spike

Let $s\in\lbrace-1,1\rbrace$, $t\gt0$, and $k(x)=\sum_i x_i$. The table

$$ R_t(x)=\frac{s t}{t+k(x)}=\frac{s}{1+\sum_i x_i/t} $$

is exactly one admissible head. Its numerator is constant, its denominator constant coefficient is positive, and every slope coefficient is positive. The existing positive-affine-ratio realization applies directly, without an approximation or a bound on embedding dimension.

At the origin $R_t(0)=s$. At every other cube point, $|R_t(x)|\leq t$. In the normalized slope chart $b_i=1/t$, the numerator is held equal to $s$, so

$$ g_t(x)_i=-\frac{s t^2 x_i}{(t+k(x))^2},\qquad E_{b}(g_t(x))=\frac{t^2 k(x)}{(t+k(x))^3}. $$

**Proof.** Differentiate $s/(1+b\cdot x)$ with respect to each $b_i$ and use $x_i^2=x_i$ and $s^2=1$. The energy is zero at the origin. Elsewhere $k\geq1$, so $k\leq(t+k)^3$ and the energy is at most $t^2$. Consequently its total unnormalized energy is at most $Nt^2$. $\blacksquare$

### Theorem 3. Arbitrarily small energy at one extra head

Let $y(x)\in\lbrace-1,1\rbrace$ denote the labels and assume $y(x)S(x)\gt0$ everywhere. Set $m=\min_x y(x)S(x)\gt0$ and $s=y(0)$. For $\varepsilon\gt0$ and $0\lt t\leq\varepsilon m/2$, define

$$ T_{\varepsilon,t}(x)=R_t(x)+\varepsilon S(x). $$

At the origin,

$$ y(0)T_{\varepsilon,t}(0)=1+\varepsilon |S(0)|\geq1. $$

At every nonzero input,

$$ y(x)T_{\varepsilon,t}(x)\geq-t+\varepsilon m\geq\varepsilon m/2\gt0. $$

Scaling each original numerator and the output bias by $\varepsilon$, then adjoining the spike, gives exactly $H+1$ admissible heads. Scaling is also immediate in the original fractional atom parameters: multiply its output parameters $\eta,\delta,m_i$ by $\varepsilon$, leaving the attention parameters unchanged. Thus the construction preserves the architecture and every label. Its squared full-table norm satisfies $G\geq1$.

For the original fixed representation, put

$$ K=\sum_{h,x}E_{b_h}\left(-\frac{A_h(x)z_h(x)}{(1+b_h\cdot z_h(x))^2}\right). $$

This is a finite nonnegative real number. There is no uniform bound on it, and none is needed. Scaling the old numerators scales their raw gradients by $\varepsilon$ and their total energy by $\varepsilon^2$. Lemmas 1 and 2 imply

$$ 0\leq V(T_{\varepsilon,t})\leq Nt^2+\varepsilon^2K. $$

Choose $t=\varepsilon m/(2(1+m))$. Then $0\lt t\leq\varepsilon m/2$ and $t\leq\varepsilon/2$. Therefore

$$ 0\leq V(T_{\varepsilon,t})\leq\varepsilon^2(K+N/4)\longrightarrow0. $$

For any prescribed $\eta\gt0$, a sufficiently small positive $\varepsilon$ gives the desired strict inequality. This proves the theorem. $\blacksquare$

If the original classifier has zero scores at negative examples, first decrease its output bias slightly. There are finitely many positive examples, so a sufficiently small decrease preserves all their positive scores and makes all negative scores strictly negative. The all-negative case can use a constant negative bias. Thus strictness adds no restriction to the target functions covered.

## Scope and consequences

As $\varepsilon\to0$ with the stated $t$, the normalized tables converge to $s\delta_0$. In particular, the closures of all strict sign classes having the same label at the origin contain this common coordinate axis, while the energy tends to zero at an overhead of one head. The small coordinates still carry the full target labeling.

The earlier [cancellation-energy construction](cancellation-energy.md) shows that normalized energy can diverge along admissible representations of a fixed two-head classifier even with bounded denominator slopes. The present theorem addresses a different quantifier: after adding one head, the energy infimum is zero for every target. Together these results preclude treating this scalar energy, by itself, as a uniform substitute for a sign-pattern count. They do not rule out arguments using additional geometric data or a constrained choice of representatives.

The construction starts from a representation of the target. It supplies no economical way to obtain that representation, no compression theorem, and no improved asymptotic lower or upper bound.

## Verification scope

`VanishingEnergySpike.lean` checks general finite Cauchy-Schwarz for this energy, quadratic scaling, the normalized bound, the exact Boolean spike energy, its bound, strict sign preservation, the norm lower bound, existence of small scales, and the spike's realization as an actual `FracAtom`. The normalization differentiation and the full finite-head assembly above are written proofs, not additional Lean declarations. The independent rational audit checks the energy identity and inequalities for explicit finite representations, including both orientations and signed cancellation. No computational check is used as evidence for an asymptotic lower bound.
