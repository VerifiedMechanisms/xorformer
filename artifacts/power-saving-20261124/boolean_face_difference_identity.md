# Boolean face differences as comparisons of utility means

## Scope and status

This note gives an exact identity for one admissible affine-ratio head and tests a possible sign-sensitive consequence. The identity holds at every Boolean face, with no approximation, margin, or coefficient bound. The proposed union-closure consequence is false, even for one head with integer coefficients. No lower bound on unrestricted head count follows here.

The proof is a written elementary argument using a convergent Laplace integral and integration by parts. The counterexample is checked by exact rational arithmetic. Neither has been Lean formalized.

## 1. Exact face identity

Fix a nonempty coordinate set $S$ and a base point with every coordinate of $S$ equal to zero. Let $A$ and $B$ denote the numerator and denominator values at that base point. Let $a_i,b_i$ be their slopes on the coordinates in $S$. Assume $B\gt0$ and $b_i\gt0$. For a function on the face define

$$ \Delta_S\phi=\sum_{U\subseteq S}(-1)^{|S|-|U|}\phi(\mathbf1_U). $$

Here the fixed coordinates outside $S$ are suppressed from the notation. Put

$$ K_S(B)=\int_0^\infty e^{-Bt}\prod_{i\in S}(1-e^{-b_it})dt. $$

The integrand is positive for positive $t$, so $K_S(B)\gt0$. Define

$$ r_i=\frac1{K_S(B)}\int_0^\infty\frac{e^{-Bt}\prod_{j\in S}(1-e^{-b_jt})}{e^{b_it}-1}dt,\qquad\theta_i=\frac{b_i r_i}{B}. $$

The apparent singularity at zero is integrable: its order is $t^{|S|-1}$. Every $r_i$ is positive.

**Theorem.** The weights satisfy $\theta_i\gt0$ and $\sum_{i\in S}\theta_i=1$, and

$$ \Delta_S\left(\frac AB\right)=(-1)^{|S|}K_S(B)B\left(\frac AB-\sum_{i\in S}\theta_i\frac{a_i}{b_i}\right). $$

In the left side, $A/B$ denotes the affine-ratio function on the whole face. In the right side, $A$ and $B$ are its base values.

**Proof.** Insert the identity $1/u=\int_0^\infty e^{-ut}dt$ for every positive denominator and interchange the finite sum with the integral. The denominator-only term gives the product of $e^{-b_it}-1$. A numerator slope $a_i$ contributes only subsets containing $i$, giving an additional factor $e^{-b_it}$ on that coordinate. Thus

$$ \Delta_S\left(\frac AB\right)=(-1)^{|S|}\int_0^\infty e^{-Bt}\prod_{i\in S}(1-e^{-b_it})\left(A-\sum_{i\in S}\frac{a_i}{e^{b_it}-1}\right)dt=(-1)^{|S|}K_S(B)\left(A-\sum_{i\in S}a_i r_i\right). $$

The function $e^{-Bt}\prod_i(1-e^{-b_it})$ vanishes at both integration endpoints. Integrating its derivative gives

$$ 0=-BK_S(B)+\sum_{i\in S}b_i\int_0^\infty\frac{e^{-Bt}\prod_{j\in S}(1-e^{-b_jt})}{e^{b_it}-1}dt. $$

Consequently $\sum_i b_i r_i=B$, proving the weight normalization and the displayed formula. $\blacksquare$

## 2. Consequences that do hold

The normalized face difference has the sign of the base ratio minus a positive weighted mean of the slope ratios. In particular it cannot be positive if the base ratio is below every slope ratio, and it cannot be negative if the base ratio is above every slope ratio.

The weights favor smaller denominator slopes. If $b_i\leq b_j$, then $\theta_i\geq\theta_j$. Indeed, for every fixed positive $t$ the function $u\mapsto u/(e^{ut}-1)$ decreases on positive $u$. Its derivative has the sign of $e^{ut}(1-ut)-1$, which is negative because its derivative with respect to $ut$ is $-ut e^{ut}$. The two weight integrals have the same remaining positive factor.

There is also a probabilistic description. Let $T_0,T_i$ be independent exponential random variables with respective rates $B,b_i$. Then $BK_S(B)$ is the probability that every $T_i$ occurs before $T_0$. Conditional on this event, $\theta_i$ is the probability that $T_i$ is the last of the clocks indexed by $S$. This follows directly by writing the density for the last clock.

For a full positive-slope denominator $b_0+\sum_i b_ix_i$, the base ratio is itself a positive weighted mean of the ratios $a_0/b_0$ and $a_j/b_j$ for the active coordinates outside $S$. Thus the exact identity compares utility means on opposite sides of the face split. Heads with negative denominator slopes admit the same statement after complementing all coordinates. Constant-denominator heads are affine and have zero face differences of order at least two.

## 3. A natural sign-closure inference fails

Take the admissible head

$$ \phi(x)=\frac{10x_1-31x_2-3x_3}{1+x_1+2x_2+3x_3}. $$

Its denominator is positive everywhere and all three slopes are strictly positive. Its numerator is unrestricted affine, as permitted by the original model. At the zero base point, exact evaluation gives

$$ \Delta_{\lbrace1,2\rbrace}\phi=\frac1{12},\qquad-\Delta_{\lbrace3\rbrace}\phi=\frac34,\qquad-\Delta_{\lbrace1,2,3\rbrace}\phi=-\frac1{210}. $$

Therefore the two disjoint sets $\lbrace1,2\rbrace$ and $\lbrace3\rbrace$ have positive normalized face differences, while their union has a negative normalized difference. In particular positive normalized face signs are not closed under disjoint union.

The newly added coordinate also has a positive utility difference from the base: the base utility is zero and $-a_3/b_3=1\gt0$. Nevertheless adding that coordinate changes a positive normalized face difference to a negative one. The weights depend on the whole face and cannot be replaced by positive coordinate weights independent of $S$.

For explicit checking, the eight values in lexicographic order $000,001,010,011,100,101,110,111$ are

$$ 0,\quad-3/4,\quad-31/3,\quad-17/3,\quad5,\quad7/5,\quad-21/4,\quad-24/7. $$

Substituting these fractions in the three alternating sums yields the claimed values.

## 4. Remaining gap

The formula gives an exact positive structure before the sum over heads. Different heads have independent weights and independent utility orders, and their signed contributions can cancel without restriction. The failed union-closure inference shows that even one head does not have the simplest additive sign structure on the Boolean face lattice. No sign-count theorem for arbitrary sums has been derived from the identity.
