# Two Pure Rotary Heads Equal Two Vanilla Heads

## Statement

Use the unchanged fixed-query models and scalar normal forms of [Theorem 14](014_rope_head_complexity.md). For every input length and every Boolean function, pure rotary and vanilla computability agree at each head count at most two.

$$ H_P(f)\leq2\quad\Longrightarrow\quad H_P(f)=H_V(f). $$

No invariance under complementing the inputs is required. This removes that assumption from [Theorem 15](015_pure_rope_two_heads_complement_invariant.md). Any strict improvement from pure RoPE, if one exists, must therefore use at least three pure heads.

The proof also gives a stronger mixed statement: a pure atom together with any positive affine fraction can be replaced, for Boolean classification, by two vanilla heads. The second fraction need not be a pure atom.

This is a complete two-head result. It does not establish the universal equality for arbitrary head counts.

## Proof

### Lemma 1. A token endpoint gives an admissible affine factor

Write a pure atom as $p=N/D$, where

$$ D(x)=\gamma+\sum_i\bigl(a_i(1-x_i)+b_ix_i\bigr),\qquad N(x)=\eta+\sum_i\bigl(a_iv_0(1-x_i)+b_iv_1x_i\bigr). $$

All $a_i,b_i,\gamma$ are strictly positive. Suppose $v_1\neq v_0$. There exist $t\in\lbrace v_0,v_1\rbrace$, $\sigma\in\lbrace-1,1\rbrace$, and an affine form $F$ such that

$$ N=tD+\sigma F,\qquad F(x)\gt0\text{ on the cube}, $$

and the slopes of $F$ are either all strictly positive or all strictly negative.

**Proof.** The two endpoint differences are

$$ F_0=N-v_0D=(\eta-v_0\gamma)+(v_1-v_0)\sum_i b_ix_i, $$

$$ F_1=v_1D-N=(v_1\gamma-\eta)+(v_1-v_0)\sum_i a_i(1-x_i). $$

If $v_1\gt v_0$ and $\eta\gt v_0\gamma$, take $F=F_0$. Its constant and every slope are strictly positive. If $v_1\gt v_0$ and $\eta\leq v_0\gamma$, take $F=F_1$. Its displayed constant is strictly positive, its displayed sum is nonnegative, and every slope is strictly negative.

If $v_1\lt v_0$ and $\eta\lt v_0\gamma$, take $F=-F_0$. Its constant and every slope are strictly positive. Otherwise take $F=-F_1$. Now $\eta-v_1\gamma\gt0$, the displayed sum after negation is nonnegative, and every slope is strictly negative. These four choices give the required $t$ and $\sigma$. $\blacksquare$

The availability of both slope orientations is essential to this short proof. Vanilla admissibility permits either orientation; it does not require all denominator slopes to be positive.

### Lemma 2. One admissible factor suffices for two heads

Let $U,Z,F,V$ be affine forms. Suppose $F$ is strictly positive on the Boolean cube and its slopes are either all strictly positive or all strictly negative. Then the classifier given by

$$ P=UZ+FV $$

has a two-head vanilla realization.

**Proof.** Choose a sufficiently small finite $\varepsilon\gt0$ so that $G=F+\varepsilon Z$ remains positive on the cube and retains the strict slope orientation of $F$. Such a choice exists because there are finitely many cube points and finitely many slope inequalities, all initially strict.

Define

$$ R=\frac{U/\varepsilon}{F}+\frac{V-U/\varepsilon}{G}. $$

Both ratios are vanilla-admissible: their denominators are positive on the cube with strictly uniform slopes, and their numerators are arbitrary affine forms. Direct multiplication gives

$$ FGR=\frac{U}{\varepsilon}G+\left(V-\frac{U}{\varepsilon}\right)F=UZ+FV=P. $$

Since $FG$ is positive, $R$ and $P$ have exactly the same Boolean classifier, including at zeros. No limiting classifier or exact simulation of the original score is asserted. $\blacksquare$

### Theorem 1. A pure head and a positive affine fraction require two vanilla heads

Consider a score

$$ S=c+\frac ND+\frac QE,\qquad D(x),E(x)\gt0\text{ on the cube}, $$

where $N/D$ is a pure atom with distinct token values and $Q/E$ is any affine fraction with positive denominator. By Lemma 1, write $N=tD+\sigma F$ and set $M=Q+(c+t)E$. Clearing the original positive denominators yields

$$ DES=DM+\sigma FE. $$

Apply Lemma 2 with $U=D$, $Z=M$, and $V=\sigma E$. Its two vanilla heads have exactly the same signs as $S$. $\blacksquare$

### Theorem 2. Removing token-value degeneracy

Given any two-head pure classifier, subtract a sufficiently small positive constant from its score. Every positive input remains positive, and every negative input becomes strictly negative. The finite cube therefore has a positive strict sign margin.

Change the first head's value $v_1$ by a sufficiently small positive amount $\tau$, chosen so that the new value differs from $v_0$. At each input this changes the score by $\tau$ times the attention mass on token-one input positions. That mass lies in $[0,1]$, so the score changes by at most $\tau$. Taking $\tau$ below the strict sign margin preserves every label. One may choose either of two distinct sufficiently small positive values of $\tau$ to avoid the single forbidden equality.

The perturbed first head satisfies Theorem 1. The second pure atom is an affine fraction with positive denominator, so two vanilla heads suffice. All parameters remain finite and real.

The same perturbation works while holding an arbitrary second affine fraction fixed. Thus the mixed statement also covers equal token values in its pure head.

Zero-head and one-head equivalence were already proved in Theorem 14. Together with $H_P\leq H_V$, the two-head conversion proves the stated equality whenever $H_P(f)\leq2$. The empty-input case is included in the formal proof. $\blacksquare$

## Formalization and architectural scope

[Atoms/TwoHeadPencil.lean](../../formalization/HeadComplexity/Atoms/TwoHeadPencil.lean) proves `CubeAffine.two_products_uniform_factor`, including a finite positive perturbation that preserves all denominator inequalities. It also proves the more general `CubeAffine.two_head_pencil` criterion.

[Results/RoPETwoHeads.lean](../../formalization/HeadComplexity/Results/RoPETwoHeads.lean) proves:

- `PureRoPEAtom.exists_uniform_endpoint` for Lemma 1.
- `vanilla_two_of_nondegenerate_pure_add_positive_fraction` for the mixed statement.
- `vanilla_two_of_pure_add_positive_fraction` for the mixed statement without the nondegeneracy assumption.
- `vanilla_two_of_pureRoPEComputable` and `pureRoPEComputable_two_iff_vanilla` for the unconditional two-head result.
- `pureRoPEComputable_iff_vanilla_of_le_two` for every head budget at most two.
- `pureRoPEHStar_eq_vanilla_of_le_two` for equality of the minima.

[Atoms/RoPEStrictness.lean](../../formalization/HeadComplexity/Atoms/RoPEStrictness.lean) proves the strictness-preserving token-value perturbation used in Theorem 2. These Lean results use the existing scalar `PureRoPEAtom` definition and conclude computability in the existing shared-embedding vanilla architecture. They introduce no modified model, `sorry`, or new axioms.

For literal rotary attention, the passage to and from pure scalar atoms uses the fixed-frequency interpolation and shared-embedding construction in Theorem 14. That architectural bridge is a separate handwritten argument there; the declarations above do not claim that rotation matrices have been formalized. Subject to that bridge, the result applies to both fixed standard and freely chosen rotary frequencies, with unrotated token-only values.

## Remaining gap for arbitrary head counts

For two heads, clearing denominators and applying Lemma 1 gives exactly two products of affine forms, with one admissible factor. Lemma 2 exploits that quadratic structure.

With three or more heads, the corresponding residual factors have higher degree. Replacing the admissible denominator by its sum with such a factor would no longer produce an affine denominator. Consequently the construction above supplies no induction preserving the original head count. The universal pure-RoPE equality remains unproved by this argument.
