# Superlinear Shattering in the Actual Head Model

## Statement

Let $\mathcal H_{n,H}$ be the Boolean functions computed by at most $H$ admissible heads in the manuscript's architecture. There is no absolute constant $C$ such that every subset of every Boolean cube shattered by this class has size at most $C nH$.

More precisely, for $q=2^s$ with $s\geq1$, set

$$ H=2q^2,\qquad M=\frac{q(q+1)s}{2},\qquad n=2M. $$

Then $\mathcal H_{n,H}$ shatters the following explicitly specified set of $M^2$ Boolean inputs:

$$ \mathcal S=\lbrace (e_r,e_j):1\leq r,j\leq M\rbrace\subset\lbrace0,1\rbrace^{2M}. $$

Every witness uses strictly positive denominator constants and slopes. In particular,

$$ \frac{|\mathcal S|}{2nH}=\frac{(q+1)s}{16q}\geq\frac{s}{16}. $$

This is a lower bound on shattering capacity, not a lower bound on worst-case head complexity. It rules out a proposed uniform linear VC estimate even for the exact architecture. It neither shatters the full cube nor disproves a bound of order $nH\log n$.

## Exact embedding mechanism

### Theorem 1. Independent replication of reciprocal queries

Fix positive poles $p_{jh}$ and arbitrary real residues $a_{jh}$ for $1\leq j\leq M$ and $1\leq h\leq H$. For each row $1\leq r\leq R$, choose an independent vector of positive parameters $\theta_{rh}$. There is an admissible $H$-head score on $R+M$ input bits satisfying

$$ T(e_r,e_j)=\sum_{h=1}^H\frac{a_{jh}}{\theta_{rh}+p_{jh}}. $$

**Proof.** For each head choose $d_h\gt0$ no greater than any of its finitely many parameters or poles. For instance, take the minimum of these numbers and one. On inputs $(x,z)\in\lbrace0,1\rbrace^R\times\lbrace0,1\rbrace^M$, define

$$ A_h(x,z)=\sum_j a_{jh}z_j,\qquad B_h(x,z)=d_h+\sum_r(\theta_{rh}-d_h/2)x_r+\sum_j(p_{jh}-d_h/2)z_j. $$

The constant and all slopes of $B_h$ are strictly positive. Therefore $A_h/B_h$ is a genuine head by the positive affine ratio construction. At a selected input, the two subtracted half-constants exactly cancel the constant:

$$ A_h(e_r,e_j)=a_{jh},\qquad B_h(e_r,e_j)=\theta_{rh}+p_{jh}. $$

Summing proves the identity. The denominator is positive on the entire cube, including inputs outside the selected layer. $\blacksquare$

### Theorem 2. Shattering multiplication

If the fixed reciprocal queries

$$ F_j(\theta)=\sum_{h=1}^H\frac{a_{jh}}{\theta_h+p_{jh}} $$

shatter their $M$ query indices using positive parameter vectors, then admissible $H$-head scores shatter all $RM$ inputs $(e_r,e_j)$ on $R+M$ bits.

**Proof.** Given any labels on the selected inputs, apply the query-shattering property separately to each row's $M$ labels. This supplies one positive vector $\theta_r$ per row. Theorem 1 realizes all of these row vectors simultaneously in different input-coordinate slopes of the same heads. Each selected score has its prescribed sign. Thresholding the score defines a Boolean function on the whole cube, so this is actual-model shattering. The inputs are distinct because their two nonzero coordinate positions recover the row and column. $\blacksquare$

## Finite-field specialization

The [Hall-selector construction](reciprocal-matching-shattering.md) supplies $H=2q^2$ reciprocal terms and $M=q(q+1)s/2$ independently prescribed query signs with signed margins greater than $1/2$. Its finite-field Hall matching and reciprocal selector inequalities are already kernel checked.

Apply Theorem 2 with $R=M$. All $M^2$ signs are independent, while the input dimension is $2M$. The displayed parameter ratio follows by substitution. Since $s$ is arbitrary, the ratio is unbounded. $\blacksquare$

This replication is stronger than merely embedding the free tests at singleton inputs. Singleton embedding supplies only $M$ sample points while also using $M$ input coordinates. Independent data rows multiply the sample size and the available parameter count by different factors, retaining the unbounded ratio.

## Audit and limits

`formalization/HeadComplexity/Results/BipartiteReciprocalShattering.lean` checks the exact embedding, sample injectivity, replication, and the unbounded ratio against the normalized parameter count $2nH$. The principal declarations are `exists_exact_bipartite_embedding`, `replicate_shattering`, and `unbounded_actual_tests_per_parameter`. Every checked declaration uses only standard foundational axioms.

No claim is made about labels at the remaining cube vertices. The construction uses one input coordinate per data row and per query. Replacing those coordinates with binary addresses would require a new construction preserving the affine numerator and denominator tables. That step is not established and is not routine.

Likewise, shattering different selected layers does not give a way to combine their scores into a representation of an arbitrary full-cube labeling. A compiler with the necessary head cost has not been proved. The requested unbounded lower bound on $n^2W(n)/2^n$ remains open in this run.
