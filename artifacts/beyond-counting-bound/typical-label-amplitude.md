# Typical Labels Require Exponentially Small Relative Amplitude Margin

## Statement and scope

Put $N=2^n$ and $m=n+1$, with $n\geq1$. Let $\mathcal F_n$ be the class in [the uniform head-cover theorem](luce-covering.md): all affine-ratio tables on the Boolean cube whose denominators are positive and have coherent nonconstant coefficients, and whose maximum absolute value is at most one. Both denominator orientations are included. Allowing zero denominator slopes enlarges the manuscript's class.

Choose a label table $f$ uniformly from $\lbrace-1,1\rbrace^N$. Fix $0\lt\delta\lt1$, and define

$$ A=12m\log(128m)+\log(4/\delta),\qquad R=11\sqrt{2A/N}. $$

Here and below logarithms are natural. With probability at least $1-\delta$, the following two conclusions hold simultaneously:

1. Every $\phi\in\mathcal F_n$ satisfies $|N^{-1}\sum_x f(x)\phi(x)|\leq R$.

2. Every finite exact-model representation $S=c+\sum_h\phi_h$ of $f$, with arbitrary target-dependent parameters, satisfies

$$ \frac{\min_x f(x)S(x)}{|c|+\sum_h\|\phi_h\|_\infty}\leq R. $$

The second assertion is independent of the number of heads. Taking $\delta=n^{-1}$ gives $R=O(\sqrt{n\log n/2^n})$. Therefore for each fixed $0\lt\beta\lt1$, the fraction of Boolean functions admitting relative amplitude margin at least $\exp(-n^\beta)$, with any finite number of heads, tends to zero.

This is a complete obstruction to a typical-target version of the proposed margin repair. It gives no new lower bound on head count. In particular it does not prove the requested unboundedness of $n^2W(n)/2^n$.

## Explicit metric entropy

The previous cover gives, for $0\lt\epsilon\leq1$, a finite cover $C(\epsilon)$ in maximum table error with

$$ |C(\epsilon)|\leq2m!(K+1)^{m-1}(2+8m/\epsilon)^m,\qquad K\leq1+\frac{128m^2}{\epsilon}\log(64m^2/\epsilon). $$

We record a deliberately loose explicit consequence:

$$ \log|C(\epsilon)|\leq6m\log(128m/\epsilon). $$

**Proof.** Write $Q=128m/\epsilon$, so $Q\geq256$, $m\leq Q$, and $64m^2/\epsilon=mQ/2\leq Q^2$. Consequently

$$ K+1\leq2+2mQ\log Q\leq2+Q^3\leq Q^4. $$

For the middle inequality use $2\log Q\leq Q$ for $Q\geq2$. Also $m!\leq Q^m$ and $2+8m/\epsilon\leq Q$. The cover size is at most $2Q^{6m-4}\leq Q^{6m}$. Discard any center whose closed error ball does not meet $\mathcal F_n$. Every remaining center then has maximum absolute value at most $1+\epsilon$. $\blacksquare$

## A finite-set tail inequality

For a deterministic real table $v$, put $Z(v)=N^{-1}\sum_x f(x)v(x)$. If $\|v\|_\infty\leq a$ and $a\gt0$, independence gives

$$ \mathbb E\exp\left(\lambda\sum_x f(x)v(x)\right)=\prod_x\cosh(\lambda v(x))\leq\exp\left(\lambda^2Na^2/2\right). $$

Indeed the power series and $(2k)!\geq2^kk!$ imply $\cosh t\leq\exp(t^2/2)$. Markov's inequality, optimized at $\lambda=t/a^2$, gives $\Pr(Z(v)\geq t)\leq\exp(-Nt^2/(2a^2))$. Apply the same argument to $-v$. Thus, for any finite nonempty family $V$ of such tables, and any $0\lt\eta\lt1$, a union bound proves

$$ \Pr\left(\max_{v\in V}|Z(v)|\gt a\sqrt{\frac{2\log(2|V|/\eta)}{N}}\right)\leq\eta. $$

The zero-amplitude case is immediate. This argument requires no assumption on head parameters or on the geometry of $V$.

## Dyadic chaining

For each integer $j\geq0$, choose the preceding finite cover $C_j=C(2^{-j})$. These covers are fixed before $f$ is sampled. They satisfy

$$ \log|C_j|\leq6m\bigl(\log(128m)+j\log2\bigr). $$

For each $\phi\in\mathcal F_n$, choose $g_j(\phi)\in C_j$ with $\|g_j(\phi)-\phi\|_\infty\leq2^{-j}$. The base tables have norm at most two. For $j\geq1$, form the finite edge family

$$ E_j=\lbrace u-v:u\in C_j,\ v\in C_{j-1},\ \|u-v\|_\infty\leq3\cdot2^{-j}\rbrace. $$

It contains every increment $g_j(\phi)-g_{j-1}(\phi)$ and has cardinality at most $|C_j||C_{j-1}|$. In particular it is nonempty. Assign failure probability $\eta_j=\delta2^{-j-1}$ to level $j$, including the base level zero. The sum of all these probabilities is $\delta$.

At the base level,

$$ \log(2|C_0|/\eta_0)\leq6m\log(128m)+\log(4/\delta)\leq A. $$

At level $j\geq1$,

$$ \begin{aligned} \log(2|E_j|/\eta_j)&\leq12m\log(128m)+6m(2j-1)\log2+\log(4/\delta)+j\log2\cr &\leq A+(12m+1)j\log2\leq A(1+j). \end{aligned} $$

The last inequality uses $(12m+1)\log2\leq12m\log(128m)\leq A$, valid for $m\geq2$. Apply the finite-set tail inequality at each level and take a countable union bound. With probability at least $1-\delta$, simultaneously for all $\phi$ and every $j\geq1$,

$$ |Z(g_0(\phi))|\leq2\sqrt{2A/N},\qquad |Z(g_j(\phi)-g_{j-1}(\phi))|\leq3\cdot2^{-j}\sqrt{2A(1+j)/N}. $$

The random sample space is finite, so no measurability issue arises from these events or from the supremum over $\phi$. For every fixed labeling, $|Z(v)|\leq\|v\|_\infty$. Hence $Z(g_J(\phi))$ tends to $Z(\phi)$, and finite telescoping followed by passage to the limit gives

$$ \begin{aligned} |Z(\phi)|&\leq\sqrt{2A/N}\left(2+3\sum_{j=1}^\infty2^{-j}\sqrt{1+j}\right)\cr &\leq\sqrt{2A/N}\left(2+3\sum_{j=1}^\infty2^{-j}(1+j)\right)=11\sqrt{2A/N}. \end{aligned} $$

The last sum is three: its partial sum through $J$ is $3-(J+3)2^{-J}$. This proves the first assertion.

This is the standard chaining mechanism behind Dudley's entropy bound, not a new probabilistic inequality. See [Sridharan's note on the covering-number bound](https://www.cs.cornell.edu/~sridharan/dudley.pdf). All constants and the finite-sample probability claim used here were proved above without importing a theorem from that note.

## All finite head counts at once

Fix a labeling in the event just proved and an arbitrary finite representation. Write $M_h=\|\phi_h\|_\infty$ and $M=|c|+\sum_hM_h$. A strict sign representation has $M\gt0$. For each nonzero $M_h$, the table $\phi_h/M_h$ belongs to $\mathcal F_n$. The signed constant table also belongs to this enlarged class. A zero-amplitude head vanishes on every vertex. Linearity and the first assertion imply

$$ |Z(S)|\leq |c|R+\sum_hM_hR=MR. $$

But $Z(S)\geq\min_x f(x)S(x)$. Division by $M$ proves the second assertion. There is no union bound over representations or over head counts in this step: the single event for the atom class controls every finite signed combination.

For $\delta=n^{-1}$ and $n\geq2$, the resulting $R$ obeys

$$ \log R=-\tfrac12n\log2+O(\log n). $$

Since $n^\beta=o(n)$, this is smaller than $-n^\beta$ for all sufficiently large $n$. At least $1-1/n$ of all labelings therefore fail the proposed relative-margin guarantee. The denominator parameters may depend on the labeling throughout. $\blacksquare$

## Why this does not settle head complexity

There is no bound on $M$ in the manuscript. Replacing a score by a positive scalar multiple changes its signed margin and $M$ by the same factor. The theorem therefore rules out a proposed conditioning guarantee, including for typical targets, rather than ruling out any head budget. Inferring a lower bound on $H$ from this conclusion would require an additional statement incompatible with the theorem's allowance of arbitrary $H$.

The target of refuting $W(n)=O(2^n/n^2)$ remains open in this run. The present route is closed unless a mechanism uses head count without assuming the disproved relative-margin repair.

## Verification

`formalization/HeadComplexity/Atoms/TypicalAmplitude.lean` proves the finite weighted dyadic sum, the finite-chain estimate, its transfer to the limiting table, the uniform-error correlation estimate, and the transfer from a single atom-correlation event to arbitrary finite head sums. In particular, `HeadComplexity.TypicalAmplitude.dyadic_chain_bound` checks the constant eleven, and `HeadComplexity.TypicalAmplitude.relative_margin_bound` checks that the head count does not enter the last step. The finite covering construction and the probability estimate are the complete written proofs above. The full probabilistic theorem is not claimed as a Lean declaration.
