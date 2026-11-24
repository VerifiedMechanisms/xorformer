# Two heads resist distributional priority compilation

## Statement and scope

Let $r$ be odd, let $n=2r$, and split the independent uniform Boolean inputs into two blocks of size $r$. Let $f$ be the agreement of the two block majorities. The written construction in `priority_vertex_compiler_obstruction.md` realizes $f$ with two genuine original heads and polynomial relative margin.

Consider a sum of $K$ deterministic decision lists plus a bias. Each list tests distinct coordinates in a prescribed order. When a test succeeds it may return an arbitrary affine function; if every test fails it may also return an arbitrary affine function. Tests may use either literal. This enlarges the deterministic priority class from the earlier note, whose successful tests returned constants.

If the sign of this sum has uniform error $\varepsilon$ against $f$, then

$$ \varepsilon\geq\frac14-\frac Kr-4\sqrt{\frac{2K}{r}}-\frac8{\sqrt r}. $$

In particular, for odd $r\geq65536$, error less than $1/8$ requires $K\gt r/8192$. Thus even a constant-error distributional compiler into this class cannot have a uniform constant overhead over original head width.

This is a written proof, not a Lean declaration. It does not obstruct a compiler with additive polynomial width or a polylogarithmic overhead at exponentially large original width. The source truth tables already have good original relative margin; they are not examples of the universal low-margin class.

## Affine thresholds and antipodal pairs

**Lemma.** On a uniform Boolean cube, every affine threshold has error at least $1/4$ against a balanced Boolean function invariant under simultaneous complementation of all coordinates.

**Proof.** Center the input coordinates as independent signs. Write the threshold score as $b+L(x)$, with $L(-x)=-L(x)$. If $b\leq0$, both members of an antipodal pair cannot have strictly positive score. On every pair with true target label at least one prediction is therefore wrong. There are one quarter as many such pairs as cube vertices, because the target is balanced and antipodally invariant. If $b\gt0$, both scores cannot be nonpositive, so the same argument applies to the false target pairs. This proof uses the original convention that positive score predicts true. $\blacksquare$

## Revealing the list paths

Evaluate all lists, revealing a coordinate only when some list first needs it. Let $Q$ be the number of distinct revealed coordinates. A fixed list reaches test number $j$ with probability $2^{-(j-1)}$, since its previous tests use distinct coordinates and prescribe one failing literal each. Its expected number of tests is at most two. Therefore

$$ \mathbb E Q\leq2K. $$

The combined evaluation is a decision tree. Conditional on any leaf, the unrevealed input bits remain independent and uniform, and every list has selected an affine output. The total score is consequently affine in the unrevealed bits.

For block $b\in\lbrace1,2\rbrace$, let $Z_b$ be the sum of the revealed signs in that block and let $Q_b$ be their number. Every newly revealed sign has conditional mean zero, even when the choice of its coordinate depends on previously revealed signs. Expanding the square and conditioning each cross term on the earlier reveal history gives

$$ \mathbb E Z_b^2=\mathbb E Q_b\leq2K,\qquad \mathbb E|Z_b|\leq\sqrt{2K}. $$

There are at most $2r$ reveals, so no unbounded stopping-time hypothesis is needed. Markov's inequality gives

$$ \Pr(Q\gt r/2)\leq4K/r. $$

## Comparing with a balanced residual target

Consider a leaf with $Q\leq r/2$. Each block has $m_b\geq r/2$ unrevealed bits. From each block retain an odd number $m_b'$ of these bits, discarding at most one. Let $g_b$ be the majority of the retained bits. The agreement target $g$ of $g_1,g_2$ is balanced and invariant under simultaneous complementation of all remaining bits. Its conditional error against the affine score is therefore at least $1/4$.

For a sum $T_m$ of $m$ independent uniform signs, its largest atom has probability at most $\sqrt{2/(m+1)}$. One elementary proof starts from

$$ \binom{2s}{s}4^{-s}\leq\frac1{\sqrt{s+1}}, $$

which follows by induction using the consecutive ratio $(2s+1)/(2s+2)$; the odd case follows from the adjacent even case. The values of $T_m$ are spaced by two.

The actual majority in block $b$ differs from $g_b$ only if the retained sum has absolute value at most $|Z_b|+1$. The extra one accounts for the possible discarded bit. This interval contains at most $|Z_b|+2$ atoms. Consequently, on the selected leaf,

$$ \Pr(f\neq g\mid\text{leaf})\leq\frac{2(|Z_1|+|Z_2|+4)}{\sqrt r}. $$

By the triangle inequality for disagreement probabilities, the conditional error against $f$ is at least $1/4$ minus this expression. Averaging over the good leaves and using zero as a lower bound on the bad leaves yields

$$ \begin{aligned} \varepsilon &\geq\frac14-\frac14\Pr(Q\gt r/2)-\frac{2(\mathbb E|Z_1|+\mathbb E|Z_2|+4)}{\sqrt r} \cr &\geq\frac14-\frac Kr-4\sqrt{\frac{2K}{r}}-\frac8{\sqrt r}. \end{aligned} $$

If $K\leq r/8192$ and $r\geq65536$, the right side is greater than $1/8$. This proves the stated linear requirement. $\blacksquare$

## Consequence for the repair search

Replacing each rational head separately by constantly many deterministic priority lists cannot supply the desired approximate repair, even when the source score already has polynomial margin. The obstruction arises before any issue about tiny denominator faces or signed cancellation across an exponential number of heads. A positive distributional repair needs a richer family of original heads, global sharing, or an additive polynomial budget. None of those possibilities is ruled out here.
