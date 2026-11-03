# Addressing Functions and Exact Small Address Counts

## Statement

Let $\mathrm{IDX}_r(a,y)=y_a$, with $r$ address bits and $2^r$ data bits. Addresses use little-endian binary order. Then

$$ \deg_{\pm}(\mathrm{IDX}_r)=r+1,\qquad H^{\ast}(\mathrm{IDX}_r)\geq r+1. $$

For $r\geq2$,

$$ H^{\ast}(\mathrm{IDX}_r)\leq2^r-1. $$

The first three nontrivial address sizes are exact:

| address bits | total input bits | threshold degree | minimum heads |
| --- | --- | --- | --- |
| 1 | 3 | 2 | 2 |
| 2 | 6 | 3 | 3 |
| 3 | 11 | 4 | 4 |

> **Improvement.** This adds exact values for a natural nonsymmetric family beyond the existing four-input classification. The general construction saves one head over the data-independent Cauchy construction. No equality with threshold degree is asserted for four or more address bits.

## Proof

### Theorem 1. Exact threshold degree

Introduce a fresh bit $z$ and identify the data input at address $b$ with $z$ when $b$ has even parity and with $1-z$ otherwise. The resulting function is parity on the address bits and $z$.

Each substituted coordinate is affine. Substitution and Boolean multilinearization cannot increase polynomial degree. Thus parity's threshold-degree lower bound gives $r+1$. Conversely, the exact selector score

$$ 2\sum_{b\in\lbrace0,1\rbrace^r}y_b\prod_{i:b_i=1}a_i\prod_{i:b_i=0}(1-a_i)-1 $$

has degree at most $r+1$ and the required strict sign.

The new `Polynomial/AffineSubstitution.lean` proves the degree-preserving substitution interface. `Results/Addressing.lean` proves this identity and the matching selector upper bound for every address count. The lower proof uses threshold degree; it does not assume arbitrary input complementation preserves attention denominators.

### Theorem 2. Data-independent denominators need all address columns

Put $m=2^r$ and encode the address as $z(a)=\sum_i2^{i-1}a_i$. A square Cauchy matrix with entries $1/(z(a)+t_h)$, for $m$ distinct positive shifts, is invertible. Affine numerators in the data bits therefore interpolate $y_a$ exactly. Subtract $1/2$ and perturb the zero data slopes of every denominator to small positive slopes. The finite classification margin persists, giving $m$ genuine heads.

Within the closure where denominators are independent of data, a score has the form

$$ b(a)+\sum_b C_{ab}y_b,\qquad C_{ab}=\sum_{h=1}^{H}\frac{\beta_{hb}}{D_h(a)}. $$

Consequently $\mathrm{rank}(C)\leq H$. Correct classification for all data vectors forces

$$ C_{aa}\gt\sum_{b\neq a}|C_{ab}|. $$

Indeed, compare the largest score with $y_a=0$ with the smallest score with $y_a=1$. The coefficient matrix is strictly diagonally dominant and therefore nonsingular. Thus $H\geq m$ in this data-independent closure.

### Theorem 3. A data-dependent perturbation saves one head

Assume $r\geq2$. Set $m=2^r$ and $H=m-1$. For $z\in\lbrace0,\ldots,m-1\rbrace$ and $h\in\lbrace1,\ldots,m-1\rbrace$, define

$$ R_{zh}=\frac1{z+h},\qquad Q(z)=\prod_{h=1}^{m-1}(z+h),\qquad V(z)=\prod_{j=0}^{m-1}(z-j),\qquad c_z=\frac{Q(z)}{V'(z)}. $$

The Cauchy columns are independent. The Lagrange leading-coefficient identity gives $c^{\top}R=0$, so their column space is $c^{\perp}$. Since $m$ is even,

$$ \mathrm{sign}(c_z)=(-1)^{z+1}. $$

Put $q=m/2$. Let $B$ be supported on the two even nodes $0,q$, with $B_0=c_q$ and $B_q=-c_0$. Then $c^{\top}B=0$, so there is a rational vector $\beta$ with $R\beta=B$.

The numerator of $\sum_h\beta_h/(z+h)$ has precisely the other $m-2$ address nodes as roots. Its leading coefficient is negative, and taking residues at the poles gives

$$ \mathrm{sign}(\beta_h)=(-1)^h. $$

Let $a_1=z\bmod2$ be the low address bit and set $U_h(a)=\beta_h a_1$. Because $B$ is supported at even nodes,

$$ \sum_h\frac{U_h(a)}{z(a)+h}=0. $$

Define $g_h(a)=-U_h(a)/(z(a)+h)^2$ and $\gamma_h=c^{\top}g_h$. Since $c_z$ is positive on odd nodes,

$$ \gamma_h=-\beta_h\sum_{z\ \mathrm{odd}}\frac{c_z}{(z+h)^2}. $$

Thus $\gamma$ has both signs. For each data coordinate $b$, choose positive rational numbers $q_{hb}$ with $\sum_h\gamma_h q_{hb}=c_b$. Such a choice is possible by increasing one coordinate of the required sign. The remaining vector lies in $c^{\perp}$, so rational coefficients $v_{hb}$ satisfy

$$ e_b=\sum_h\left(\frac{v_{hb}}{z+h}+q_{hb}g_h\right). $$

Use the $m-1$ fractions

$$ D_h=z(a)+h+\varepsilon\sum_bq_{hb}y_b,\qquad N_h=\varepsilon^{-1}U_h(a)+\sum_bv_{hb}y_b. $$

Every denominator coefficient is strictly positive. The order $1/\varepsilon$ terms cancel, while the finite term of the sum is exactly $y_a$. The remaining error is uniformly $O(\varepsilon)$ on the finite cube. Replace $N_1$ by $N_1-D_1/2$ to subtract the constant $1/2$, and choose a sufficiently small positive rational $\varepsilon$. The strict classifier is preserved. Therefore $H^{\ast}(\mathrm{IDX}_r)\leq2^r-1$. $\blacksquare$

The supplemental [exact construction verifier](../../artifacts/calculations/verify_automlr_constructions.py) checks the residue identities through five address bits and the complete perturbed classifiers through three address bits. The argument above proves the general statement; these finite tests are supporting checks.

### Theorem 4. Exact small head counts

The one-address-bit case has an exact two-head integral certificate. For two address bits, three positive-oriented denominators and integral affine numerators give a strict certificate on all $64$ inputs. For three address bits, one positive-oriented and three negative-oriented denominators give a strict certificate on all $2048$ inputs.

The complete coefficient rows are small Lean constants in [AddressingCertificates.lean](../../formalization/HeadComplexity/Results/AddressingCertificates.lean). The kernel checks denominator orientation and every cleared-score sign using ordinary integer arithmetic. `IntegralClearedScoreCertificate` then compiles the checked data to actual attention heads. The lower bound from Theorem 1 proves optimality in every case.

## Formal and Subsumption Status

The general threshold-degree formula and the three exact head counts are kernel-checked. The general $2^r-1$ construction and the data-independent lower bound are proved above; they are not yet Lean declarations.

`HeadComplexity/AutomlrSubsumption.lean` compares the two new exact cases with the general degree-sensitive bounds specialized to these functions. It certifies that equality to $3$ strictly strengthens the interval from $3$ to $16$, and equality to $4$ strictly strengthens the interval from $4$ to $176$. Both comparisons retain equality of the exposed head scalar with the actual `HStar` value as their common requirement.
