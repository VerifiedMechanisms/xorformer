# Two Pure Rotary Heads For Complement-Invariant Functions

## Statement

Let $H_P$ and $H_V$ denote pure rotary and vanilla head complexity under the conventions of [Theorem 14](014_rope_head_complexity.md). Suppose $f$ is invariant under complementing every input bit:

$$ f(1-x)=f(x). $$

Then

$$ H_P(f)\leq2\quad\Longrightarrow\quad H_P(f)=H_V(f). $$

This holds with either fixed standard rotary frequencies or freely chosen frequencies. Consequently a strict two-head pure-RoPE improvement, if one exists, must be a function that is not invariant under simultaneous input complementation, and its counts must be exactly two versus three.

This does not supply a strict Boolean head-count example. It excludes a substantial candidate class beyond the fully symmetric functions already covered by Theorem 14.

## Proof

The empty-input case is constant. Assume $n\geq1$. It suffices to show that a complement-invariant two-head pure rotary classifier has a two-head vanilla realization. Equality of the minima then follows from $H_P\leq H_V$ and the common zero-head and one-head characterizations.

### Lemma 1. A pure head has a special numerator direction

Write $z_i=2x_i-1$. For a pure atom with weights $a_i,b_i,\gamma\gt0$, set

$$ d_0=\gamma+\frac12\sum_i(a_i+b_i),\qquad s_i=\frac{a_i+b_i}{2d_0},\qquad \beta_i=\frac{b_i-a_i}{2d_0}. $$

Its denominator is $d_0(1+\beta\cdot z)$, and

$$ |\beta_i|\lt s_i,\qquad \sum_i s_i\lt1. $$

Write its normalized numerator as $N+A\cdot z$. The token-only values imply

$$ A_i=ks_i+\ell_0\beta_i,\qquad k=\frac{v_1-v_0}{2},\qquad \ell_0=\frac{v_1+v_0}{2}. $$

After absorbing $N$ into the score constant, the remaining numerator direction is

$$ u=A-N\beta=ks+\ell\beta,\qquad \ell=\ell_0-N. $$

Thus the head has the normalized form $N+(u\cdot z)/(1+\beta\cdot z)$, with the displayed relation between $u,s,\beta$.

### Lemma 2. The numerator direction permits a positive denominator direction

Suppose $|\beta_i|\lt s_i$, $\sum_i s_i\lt1$, and $u=ks+\ell\beta$ with $k\gt0$. There are $e\in\lbrace-1,1\rbrace$ and $\lambda\in\mathbb R$ such that

$$ c=e\beta+\lambda u,\qquad c_i\gt0,\qquad \sum_i c_i\lt1. $$

**Proof.** Put $S=\sum_i s_i$ and $B=\sum_i\beta_i$.

If $\ell\gt k(S-B-1)$, take

$$ e=-1,\qquad \lambda=\frac1{k+\ell},\qquad c=\frac{k}{k+\ell}(s-\beta). $$

The inequality implies $k+\ell\gt k(S-B)\gt0$. Every coordinate of $c$ is positive, and its sum is below one.

Otherwise, $\ell\leq k(S-B-1)\lt k(1-S-B)$ because $S\lt1$. Take

$$ e=1,\qquad \lambda=\frac1{k-\ell},\qquad c=\frac{k}{k-\ell}(s+\beta). $$

Now $k-\ell\gt k(S+B)\gt0$, and the same conclusions follow. The claimed relation to $\beta,u$ follows by substitution in either case. $\blacksquare$

If $k\lt0$, replace $u,k,\ell$ by their negatives and negate $\lambda$ afterward. Thus the conclusion holds whenever $k\neq0$.

### Lemma 3. Complement invariance produces a quadratic sign representation

Make the two-head score strict by lowering its threshold constant a sufficiently small amount. Since the cube is finite, a further sufficiently small perturbation of the first head's token value preserves all labels and ensures $v_1\neq v_0$. This justifies using Lemma 2 even when the original token values coincide. These are finite real parameters; no limiting classifier is used.

By Lemma 1, the resulting score has the form

$$ S(z)=T+\frac{u\cdot z}{1+\beta\cdot z}+\frac{w\cdot z}{1+\delta\cdot z},\qquad \sum_i|\beta_i|\lt1,\qquad \sum_i|\delta_i|\lt1. $$

The first head satisfies $u=ks+\ell\beta$ with $k\neq0$. Clear the two positive denominators to obtain a strict sign polynomial $P$. Since $f(-z)=f(z)$, the polynomials $P(z)$ and $P(-z)$ have the same target sign. Both weights $1\pm\beta\cdot z$ are positive, so the following weighted average also has that sign:

$$ Q(z)=\frac{(1-\beta\cdot z)P(z)+(1+\beta\cdot z)P(-z)}2=T\bigl(1-(\beta\cdot z)^2\bigr)+(u\cdot z)(v\cdot z),\qquad v=\delta-\beta. $$

### Lemma 4. Reorientation preserves the quadratic polynomial

Apply Lemma 2 to obtain $c=e\beta+\lambda u$ with positive coordinates and sum below one. Set

$$ v'=v+T(2e\lambda\beta+\lambda^2u). $$

Using $e^2=1$, expansion gives the exact identity

$$ Q(z)=T\bigl(1-(c\cdot z)^2\bigr)+(u\cdot z)(v'\cdot z). $$

No sign approximation occurs in this step.

### Lemma 5. The reoriented polynomial has a two-head vanilla realization

Choose $\varepsilon\gt0$ sufficiently small that $q=c+\varepsilon v'$ still has positive coordinates and sum below one. Consider

$$ R(z)=T+\frac{(u/\varepsilon)\cdot z}{1+c\cdot z}+\frac{(-u/\varepsilon-T(c+q))\cdot z}{1+q\cdot z}. $$

Direct multiplication yields

$$ (1+c\cdot z)(1+q\cdot z)R(z)=T\bigl(1-(c\cdot z)^2\bigr)+(u\cdot z)(v'\cdot z)=Q(z). $$

Both denominators are positive on the cube. In bit coordinates their constants are $1-\sum_i c_i\gt0$ and $1-\sum_i q_i\gt0$, and all their slopes are strictly positive. The vanilla affine-fraction normal form therefore realizes each ratio with one head. This proves $H_V(f)\leq2$. $\blacksquare$

## Formalization scope

[Atoms/RoPEReorientation.lean](../../formalization/HeadComplexity/Atoms/RoPEReorientation.lean) checks the new algebraic ingredients:

- `PureRoPEAtom.abs_centerBias_lt_centerMass`, `sum_centerMass_lt_one`, and `centerSlope_sub_eq` verify the special pure-head coefficients used in Lemma 1.
- `RoPEReorientation.exists_positive_direction` and `exists_positive_direction_of_ne_zero` prove Lemma 2, including the strict positivity and sum bound.
- `RoPEReorientation.weighted_antipodal_average` and `quadric_reorientation` verify the two polynomial identities.

The complete head-count theorem in this note remains handwritten. In particular, the finite strictness-preserving perturbation and the assembly of these identities with the two-head vanilla construction are not a Lean declaration. No existing architectural definition has been changed.

The weighted-average method and positive-direction two-head construction were informed by [Theorem 199 in run 15dee8652f45](https://github.com/VerifiedMechanisms/xorformer-runs/blob/ar/15dee8652f45/theorems/06_strict_separations/199_complement_invariant_two_head_criterion.md). The pure-head pencil relation and its reorientation supply the additional argument needed here.
