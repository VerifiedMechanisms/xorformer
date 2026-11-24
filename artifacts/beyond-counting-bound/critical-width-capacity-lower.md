# Capacity at Exponential Head Width

## Statement and status

This construction was supplied by the asker during the continuation and is audited here directly. It is a lower bound on the number of computable truth tables, not a lower bound on worst-case head complexity. It uses actual admissible heads with strictly positive denominator slopes, arbitrary affine numerators, and a free final bias.

Let $N=2^n$, let $H\geq1$, and set

$$ a=\left\lfloor\frac{N}{64nH}\right\rfloor,\qquad b=n-a. $$

Assume $1\leq a\leq n/2$. Write $\mathcal F_{n,H}$ for all Boolean truth tables computable with at most $H$ heads in the unchanged model.

**Theorem 1.** Under these hypotheses,

$$ \log_2|\mathcal F_{n,H}|\geq\frac{Hb}{4}\log_2(a/4+1)\geq\frac{Hn}{8}\log_2\left(\frac{N}{512nH}\right). $$

Consequently, for each fixed real $1\lt x\lt2$, if $H=\lfloor2^n/n^x\rfloor$, then for all sufficiently large $n$,

$$ \log_2|\mathcal F_{n,H}|\geq\frac{x-1}{16}Hn\log_2 n. $$

Thus a critical-width upper bound of order $nH$ is false. This theorem remains compatible with an upper bound of order $nH\log n$, which would be sufficient for an improved worst-case lower bound. The latter upper bound is not proved here.

## Separated centers and deletion stars

For an integer $m\geq1$, take $k=\lceil\log_2(m+1)\rceil$ and choose $m$ distinct nonzero columns in $\mathbb F_2^k$. The syndrome map partitions the $m$-cube into at most $2^k\leq2(m+1)$ cosets. Two distinct vectors in the same coset cannot have Hamming distance one, since no column is zero, or distance two, since the columns are distinct.

At least $2^{m-1}$ cube vertices have support size at least $m/4$. Indeed, complementation pairs all vertices, and at least one member of each pair has weight at least $m/2$. One syndrome coset therefore supplies a collection $\mathcal C_m$ of at least

$$ \frac{2^m}{4(m+1)} $$

centers, all of support size at least $m/4$, with pairwise distance at least three. Supports in this collection are nonempty. For a center $S$, define its lower deletion star

$$ D(S)=\lbrace S\setminus\lbrace i\rbrace:i\in S\rbrace. $$

These stars are pairwise disjoint. If two of them shared a point, their centers would differ in at most two positions.

Use this construction in disjoint blocks of sizes $a$ and $b$. The product stars $D(S)\times D(T)$, for $S\in\mathcal C_a$ and $T\in\mathcal C_b$, are disjoint. Their number is at least

$$ \frac{N}{16(a+1)(b+1)}\geq2H. $$

For the last inequality, put $R=N/(64nH)$. Since $a=\lfloor R\rfloor\geq1$, we have $a+1\leq2a\leq2R$. Also $b+1\leq n$. Hence $16(a+1)(b+1)\leq32nR=N/(2H)$. Retain any $H$ cells.

## An ordering that permits exact successive programming

Process the retained centers $(S,T)$ in decreasing order of $|S|+|T|$, breaking ties arbitrarily. No point of an earlier cell lies in the current center's downset.

To prove this, suppose $S'\setminus\lbrace i\rbrace\subseteq S$. If $S\neq S'$ and $|S|\leq|S'|$, the two centers differ in at most two coordinates, contradicting the coset distance. Therefore either $S=S'$ or $|S|\geq|S'|+1$. The same assertion holds in the second block. If an earlier cell point lay below the current center in both blocks, then either the two centers would agree, or the current total weight would be strictly larger. Both alternatives contradict distinctness and the chosen order.

Now fix a current cell and write $s=|S|$, $t=|T|$. Enumerate the coordinates of $S$ with values $u_i=1,\ldots,s$. Independently for every $j\in T$, choose $k_j\in\lbrace0,\ldots,s\rbrace$ and put $v_j=-k_j-1/2$. Define the affine numerator

$$ A(z)=\sum_{i\in S}u_i(1-z_i)+\sum_{j\in T}v_j(1-z_j). $$

At the cell point deleting $i$ and $j$, its value is $u_i+v_j$. It is never zero and is positive exactly when $u_i\gt k_j$. Thus these choices give exactly $(s+1)^t$ distinct sign tables on the cell.

For $\tau\gt0$, set

$$ B_\tau(z)=1+\sum_{i\in S\cup T}z_i+\tau\sum_{i\notin S\cup T}z_i. $$

All variable slopes are strictly positive and the denominator is at least one throughout the cube. On the current cell it has the constant value $s+t-1\geq1$, independently of $\tau$. Off the current downset it is at least $\tau$.

Let $G$ be the score already constructed. First choose a positive scalar $\lambda$ so large that

$$ \frac{\lambda}{2(s+t-1)}\gt1+\max_{z\text{ in current cell}}|G(z)|. $$

Then $G+\lambda A/B_\tau$ has the desired strict signs on the new cell for every $\tau\gt0$. On the union of the earlier cells, let $\gamma$ be the minimum current absolute score and let $C$ be the maximum of $|A|$. The induction hypothesis gives $\gamma\gt0$. Every such point is outside the current downset, so choosing

$$ \tau\gt1+2\lambda C/\gamma $$

preserves all earlier signs. At the first step there are no earlier constraints and any positive $\tau$ suffices. This constructs one admissible head per retained cell, by finite choices of real parameters.

After the final step, all programmed scores are strictly nonzero. Choose a bias whose magnitude is less than half their minimum absolute value and which avoids the finitely many negatives of the other scores. This preserves every programmed sign and removes every remaining zero. It uses the free readout bias, not another head.

## Counting and rounding

The independent cell choices give different final full truth tables, since all their programmed signs are preserved. Each cell has $s\geq a/4$ and $t\geq b/4$. Consequently

$$ \log_2|\mathcal F_{n,H}|\geq\sum_{\text{retained }(S,T)}|T|\log_2(|S|+1)\geq\frac{Hb}{4}\log_2(a/4+1). $$

We have $b\geq n/2$ and $a/4+1\geq R/8=N/(512nH)$. If the logarithm of the latter quantity is nonnegative, these inequalities give the claimed second bound. If it is negative, that bound follows from the nonnegative first bound. This handles the entire stated integer range.

For fixed $1\lt x\lt2$, the choice $H=\lfloor N/n^x\rfloor$ eventually satisfies $N/(2n^x)\leq H\leq N/n^x$. Thus $R$ lies between $n^{x-1}/64$ and $n^{x-1}/32$. It tends to infinity and is $o(n)$, proving $1\leq a\leq n/2$ eventually. Moreover,

$$ \log_2\left(\frac{N}{512nH}\right)\geq(x-1)\log_2 n-9\geq\frac{x-1}{2}\log_2 n $$

for all sufficiently large $n$. Substituting proves the last assertion. $\blacksquare$

## Relation to the weighted curve mechanism

The [weighted curve count](weighted-curve-jet-count.md) proves that a fixed one-curve order budget has VC dimension at most $24(n+1)M$. The theorem above concerns the number of full truth tables, not shattered dimension, so it must not be substituted directly as a VC lower bound. Sauer's inequality introduces an additional logarithm when converting a VC upper bound into a full-cube growth bound. No new lower bound on a curve conversion cost at critical width is inferred here.

## Verification boundary

This file gives a complete written proof, including finite parameter choices and exact-model transfer. It is not a new Lean theorem. The asker reports exact rational small-instance checks; those are reported evidence, not computations rerun in this checkpoint. The model, complexity definitions, and current fixed-exponent target have not changed. An unrestricted lower bound improving the exponent two remains open in this run.
