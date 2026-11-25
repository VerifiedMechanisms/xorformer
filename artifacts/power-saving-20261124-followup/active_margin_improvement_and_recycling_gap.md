# Active margin improvement and the support recycling gap

## Kernel-checked local improvement

Let $S=b+\sum_{h=1}^H\phi_h$ be a strict original-model representation, let $D=|b|+\sum_h\|\phi_h\| _\infty$, and let $\gamma=\min_x f(x)S(x)/D$. Let a correction $T=d+\sum _{j=1}^K\psi_j$ have full-cube amplitude $E=|d|+\sum_j\|\psi_j\| _\infty$.

Suppose every active vertex satisfies

$$ f(x)S(x)=\gamma D\quad\Longrightarrow\quad f(x)T(x)\gt\gamma E. $$

Then for some $\epsilon\gt0$, the original admissible representation $S+\epsilon T$ at width $H+K$ preserves the entire truth table and has strictly larger relative margin. This is `HeadComplexity.ActiveMarginImprovement.exists_strict_margin_improvement` in `Research/ActiveMarginImprovement.lean`.

**Proof.** Put $a_x=f(x)S(x)-\gamma D\geq0$ and $b_x=f(x)T(x)-\gamma E$. If $a_x=0$, the assumed strict inequality makes $a_x+\epsilon b_x$ positive for every positive $\epsilon$. If $a_x\gt0$, it remains positive for all sufficiently small positive $\epsilon$. Finiteness supplies one common step. The new amplitude is at most $D+\epsilon E$, so every new signed score exceeds $\gamma$ times the actual new amplitude. The proof scales genuine heads and concatenates their lists; it introduces no inadmissible denominator.

In particular, a correction with $f(x)T(x)=1$ on the active set and amplitude $E\lt1/\gamma$ gives a strict local improvement. The theorem gives neither a lower bound on the improvement nor a bounded-width iteration.

## An abstract obstruction to generic support recycling

The following is a written counterexample for an abstract atom dictionary. It is **not an original xorformer counterexample**. It shows that efficient active interpolation, even with exact outside control, cannot by itself justify a constant-overhead endpoint.

Take a set $X$ of even cardinality $M$, a balanced sign table $f$, and a distinguished positive vertex $x_0$. Choose $0\lt\epsilon\lt1/2$. Set $r(x_0)=1$ and choose all other $r(x)$ distinct in $[\epsilon,2\epsilon]$. Let $v(x)=f(x)r(x)$, so $\|v\|_\infty=1$.

Fix a positive integer $d$. The dictionary consists of $v$ and every function supported on at most $d$ vertices with supremum norm at most one. Scores have a free bias and arbitrary real atom coefficients, and their amplitude is the absolute bias plus the sum of the individual atom norms. The single atom $v$ strictly represents $f$.

Consider any representation using at most $K$ atoms, where $Kd\lt M/2-1$. Combine all copies of $v$ into one coefficient $a$. The other atoms affect a set $U$ of at most $Kd$ vertices. There are both a positive vertex $p\neq x_0$ and a negative vertex $q$ outside $U$. Their scores are $ar(p)+b$ and $-ar(q)+b$. Strict separation implies $a\gt0$. If $D$ is the representation's amplitude and $\gamma$ its relative margin, then

$$ 2\gamma D\leq ar(p)+b+ar(q)-b\leq4\epsilon a\leq4\epsilon D. $$

Thus **every** representation of width at most $K$ has relative margin at most $2\epsilon$. This is a quantifier over all choices of atoms, coefficients, and bias in this abstract dictionary.

Nevertheless, its active set has at most $dK+2$ vertices. On $U$ there are at most $dK$ vertices. Outside $U$, the signed scores $ar(x)+b$ within the positive class and $ar(x)-b$ within the negative class are each distinct, because $a\gt0$ and the radii are distinct. At most one vertex of each class can attain the global minimum.

Every active set $A$ admits an exact correction equal to $f$ on $A$ and zero elsewhere: partition $A$ into pieces of size at most $d$ and use one sparse atom per piece. This uses at most

$$ \left\lceil\frac{|A|}{d}\right\rceil\leq K+2 $$

atoms, with total amplitude at most $K+2$. If $2\epsilon(K+2)\lt1$, this correction strictly improves the margin by the local theorem. It has perfect outside control and uniformly bounded coefficient sizes.

Even so, no constant multiple of the original width one can reach margin larger than $2\epsilon$ as $M$ grows. A healthy universal representation exists at width $\lceil M/d\rceil$: partition the whole table into $d$-point pieces, giving unit gap and amplitude at most $\lceil M/d\rceil$. Taking $\epsilon$ sufficiently small separates these margin scales arbitrarily far.

## Precise missing original-model ingredient

The abstract example has small active sets, constant-factor active interpolation, bounded correction mass, exact zero outside the active set, and a strict improvement whenever the current margin is small. These facts still allow many successive active sets and accumulated support.

A successful original-model argument must therefore prove more than those properties. It needs a geometric support-recycling theorem, a quantitative global progress bound compatible with the width budget, or an upper count for the truth tables excluded from such an endpoint. The finite local-improvement theorem establishes none of these alternatives.

## Verification status

The five declarations in `AuditActiveMarginImprovement.lean` pass the transitive axiom check with only `propext`, `Classical.choice`, and `Quot.sound`. The module build completed successfully with 3284 jobs. The abstract recycling counterexample is a written proof, independently audited by the unrestricted-capacity agent, including the free-bias inequality and the quantifier over every bounded-width representation.
