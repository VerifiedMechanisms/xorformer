# Weighted Paired-Product Thresholds

## Status and scope

This investigation studies sign inputs and sign outputs:

$$ f_w(x,y)=\mathrm{sgn}\left(\sum_{i=1}^4 w_i x_i y_i\right), \qquad x,y\in\lbrace-1,1\rbrace^4. $$

The Boolean classifier is the indicator that the displayed score is positive. Throughout the proved chamber classification, the score is nonzero on every vertex:

$$ w\cdot z\neq0 \qquad\text{for all }z\in\lbrace-1,1\rbrace^4. $$

Let the absolute coefficients, after a permutation of coordinate pairs, satisfy

$$ a\geq b\geq c\geq d\geq0. $$

The following results hold for every choice of coefficient signs.

Equivalently, the complete answer on this nonvanishing domain is

$$ \boxed{H^{\ast}(f_w)=\begin{cases}3,&|a-b-c|\lt d,\cr2,&|a-b-c|\gt d.\end{cases}} $$

Equality implies a signed-sum tie and is outside the requested domain.

| Coefficient condition | Essential pair products | Head complexity |
| --- | --- | --- |
| $a\gt b+c+d$ | One | Exactly $2$ |
| $a\lt b+c+d$ and $a+d\gt b+c$ | Four | Exactly $3$ |
| $a+d\lt b+c$ | Three | Exactly $2$ |

All signed-sum ties are excluded. All three rows are realized by open subsets of coefficient space.

> **What is established.** All nonvanishing coefficient choices are classified: head complexity is three exactly when all four pair products are essential, and two otherwise. The rank obstruction detects the number of essential pair products. Explicit admissible certificates supply the matching upper bounds, including the three-essential-pair case.

> **Boundary convention.** The requested scope explicitly excludes ties and classifies Boolean-valued sign functions only. On a signed-sum hyperplane, the usual sign function takes value zero. Assigning a Boolean value at zero defines a different problem and can destroy the separate block-odd symmetries used below. Those boundaries and the origin are outside this classification.

## Chamber reduction

Write $z_i=x_i y_i$ and $\epsilon_i=\mathrm{sgn}(w_i)$ when $w_i\neq0$. For a zero coefficient choose $\epsilon_i=1$. Put $r_i=\epsilon_i z_i$.

The substitution into $r$ is used to analyze truth tables. It is not an assumption that independently complementing input bits preserves head complexity. The model's denominator-orientation constraint prevents that shortcut. Upper bounds for different sign patterns are verified separately below.

### Proposition 1. Three possible unsigned truth tables

In sorted absolute-coefficient coordinates, every nonvanishing score has one of the following sign tables:

$$ \begin{aligned} a\gt b+c+d &: \quad f=r_1, \cr a\lt b+c+d, a+d\gt b+c &: \quad f=\mathrm{sgn}(2r_1+r_2+r_3+r_4), \cr a+d\lt b+c &: \quad f=\mathrm{sgn}(r_1+r_2+r_3). \end{aligned} $$

**Proof.** The first case is dominance of the largest coefficient. Suppose it fails. Since ties are excluded, $a\lt b+c+d$. A positive set containing one coordinate loses to its complement; a positive set containing three coordinates wins.

It remains to compare two-element sets with their complements. Sorting gives

$$ a+b\geq c+d, \qquad a+c\geq b+d, $$

and both inequalities are strict by the nonvanishing hypothesis. Thus the pairs containing the largest coordinate and either the second or third coordinate win. The remaining comparison is between $a+d$ and $b+c$.

If $a+d\gt b+c$, a two-element set wins exactly when it contains the first coordinate. This is the sign table of weights $(2,1,1,1)$. If $a+d\lt b+c$, a two-element set wins exactly when it contains two of the first three coordinates. This is majority on the first three products, independent of the fourth. These cases exhaust the possibilities. $\blacksquare$

The unsigned essential-product counts are respectively one, four, and three. Applying the coordinate signs to the truth tables does not change those counts.

## The rank invariant in Stefano's argument

The lower-bound strategy follows [Stefano's 16 September sketch in the theory channel](https://formalverific-lsu5061.slack.com/archives/C0BBX3H1KT2/p1789543672507289). The weighted averaging identity supplies the rank-three step explicitly. The coefficient-space reduction and upper-bound certificates below complete the family investigation.

For any nonvanishing weighted paired-product threshold on $k$ pairs, define its minimum bilinear representation rank by

$$ r_{\mathrm{bil}}(f):=\min\left\lbrace\mathrm{rank}(M):\mathrm{sgn}(x^{\top}My)=f(x,y)\text{ on the sign cube}\right\rbrace. $$

This is a rank of coefficient matrices restricted to bilinear representations. It should not be confused with unrestricted sign-rank of the truth-table matrix.

### Proposition 2. Bilinear rank equals the number of essential products

Let $E$ be the set of indices on which the sign function of the products actually depends. Then

$$ r_{\mathrm{bil}}(f_w)=|E|. $$

An equivalent test for membership is

$$ i\in E \quad\Longleftrightarrow\quad |w_i|\gt\min_{z_j\in\lbrace-1,1\rbrace, j\neq i}\left|\sum_{j\neq i}w_jz_j\right|. $$

**Proof.** The test says exactly that there is an assignment of the other products for which flipping the selected product crosses the threshold. Ties are absent.

Fix any bilinear representation $x^{\top}My$ and any essential index $i$. Choose a pivotal assignment of the other products. Under this restriction,

$$ f_w(x,y)=\epsilon_i x_i y_i. $$

Set $y_i=1$. All other $y_j$ remain arbitrary: choose $x_j$ to keep the prescribed other products fixed. Comparing the two scores at $x_i=1$ and $x_i=-1$ gives

$$ \epsilon_i\left(M_{ii}+\sum_{j\neq i}M_{ij}y_j\right)\gt0. $$

Minimizing over the other signs yields

$$ \epsilon_iM_{ii}\gt\sum_{j\neq i}|M_{ij}|. $$

The principal submatrix indexed by $E$, after multiplying its rows by the corresponding $\epsilon_i$, is strictly row diagonally dominant with positive diagonal. It is nonsingular, so $\mathrm{rank}(M)\geq|E|$.

Conversely, average the original linear score in the product variables over the inessential coordinates. Every summand has the same strict sign because the function is independent of those coordinates. The resulting score is

$$ \sum_{i\in E}w_i x_i y_i, $$

which still strictly sign-represents the function and has coefficient-matrix rank $|E|$. This proves equality. $\blacksquare$

### Proposition 3. Two heads imply bilinear rank at most three

Suppose a sign function has the separate block-odd symmetries

$$ f(-x,y)=-f(x,y), \qquad f(x,-y)=-f(x,y). $$

If two heads compute it, then

$$ r_{\mathrm{bil}}(f)\leq3. $$

**Proof.** A finite-domain threshold shift makes the representation strict. By the [linear-fractional normal form](../../../theorems/01_foundations_and_normal_form/010_linear_fractional_normal_form.md), normalize the positive denominator constants and absorb numerator constants into a scalar $t$ to obtain

$$ S(z)=t+\frac{u(z)}{1+b(z)}+\frac{v(z)}{1+d(z)}, \qquad z=(x,y), $$

where $u,v,b,d$ are homogeneous linear forms. Since denominator positivity holds also at $-z$, both $1+b(z)$ and $1-b(z)$ are positive.

Clearing denominators gives

$$ P=t(1+b)(1+d)+u(1+d)+v(1+b). $$

Since $f(-z)=f(z)$, the following positive weighted average retains its strict signs:

$$ Q(z):=\frac{(1-b(z))P(z)+(1+b(z))P(-z)}{2}=t(1-b(z)^2)+u(z)(d(z)-b(z)). $$

Put $e=d-b$. Apply the separate block-odd projection:

$$ R(x,y):=\frac{Q(x,y)-Q(-x,y)-Q(x,-y)+Q(-x,-y)}{4}. $$

Each signed summand has the target sign. This projection removes the constant and the pure-block quadratic terms. Writing each linear form in its $x$ and $y$ components gives

$$ R(x,y)=x^{\top}My, \qquad M=u_xe_y^{\top}+e_xu_y^{\top}-2t b_xb_y^{\top}. $$

The matrix is a sum of three rank-one matrices. Hence $\mathrm{rank}(M)\leq3$. $\blacksquare$

The weighted average is essential to this proof. Simply clearing the two denominators gives four mixed outer products and does not produce the required contradiction in dimension four. Further averaging over independent pair flips can increase matrix rank and cannot be used to preserve the rank-three bound.

## Exact head bounds

### Proposition 4. The dominant-pair chamber has exactly two heads

In the first chamber, $f_w=\epsilon_1x_1y_1$. This is equality or inequality on one pair, with the other coordinates inessential. Two-bit parity, output-complement invariance, and [dummy-variable invariance](../../../theorems/02_complexity_measure_upper_bounds/028_restrictions_and_sign_rank.md) give

$$ H^{\ast}(f_w)=2. \qquad\blacksquare $$

### Proposition 5. The four-essential-pair chamber has exactly three heads

Propositions 2 and 3 give $H^{\ast}(f_w)\geq3$ because $r_{\mathrm{bil}}(f_w)=4$.

For the matching upper bound, the chamber reduction identifies the sign table with weights $(2\epsilon_1,\epsilon_2,\epsilon_3,\epsilon_4)$. Output complementation makes the distinguished coefficient positive. Permuting the other three pairs leaves only four cases, represented by

$$ (2,1,1,1), \quad (2,1,1,-1), \quad (2,1,-1,-1), \quad (2,-1,-1,-1). $$

The [certificate archive](weighted_pair_head_certificates.json) contains an integer three-head certificate for each case. These are certificates in bit coordinates

$$ q=(\xi_1,\ldots,\xi_k,\eta_1,\ldots,\eta_k), \qquad x_i=1-2\xi_i, \qquad y_i=1-2\eta_i. $$

Each certificate lists affine numerators $A_h$ and denominators $D_h$, with the constant coefficient first. The score is

$$ S(q)=\sum_{h=1}^3\frac{A_h(q)}{D_h(q)}. $$

Every denominator is positive on the whole bit cube, and all its slopes have one common strict sign. Thus every ratio is an admissible head by [denominator orientation](../../../theorems/02_complexity_measure_upper_bounds/032_denominator_orientation.md).

The [exact verifier](verify_weighted_pair_phase_diagram.py) clears denominators and checks every one of the $256$ vertices for each certificate. The minimum signed integer margins are:

| Representative weights | Minimum signed cleared score |
| --- | ---: |
| $(2,1,1,1)$ | $2824$ |
| $(2,1,1,-1)$ | $1713446$ |
| $(2,1,-1,-1)$ | $38720$ |
| $(2,-1,-1,-1)$ | $75932$ |

All four margins are strictly positive. Permutations of coordinate pairs and output complementation preserve head complexity, so the certificates cover every signed instance of this chamber. Therefore

$$ H^{\ast}(f_w)=3. \qquad\blacksquare $$

### Proposition 6. The three-essential-pair chamber has exactly two heads

The reduced function is a signed majority of three products. It has a pivotal-pair XOR or equality restriction, hence threshold degree at least two. Its displayed quadratic gives the matching degree upper bound. In particular,

$$ H^{\ast}(f_w)\geq\deg_{\pm}(f_w)=2. $$

After output complementation and pair permutation, two representatives suffice:

$$ (1,1,1), \qquad (1,1,-1). $$

The archive supplies two-head certificates with minimum signed cleared scores $418338$ and $14933240$, respectively. The verifier checks all $64$ inputs for each. Dummy-variable invariance lifts these bounds to the full eight-input family. Thus

$$ H^{\ast}(f_w)=2. \qquad\blacksquare $$

The bilinear rank is exactly three, so these examples attain the rank-three cap for two heads. Rank-three representability by itself is not a general sufficiency theorem. The explicit head certificates establish sufficiency for these particular truth tables.

### Construction behind the two-head certificates

The weighted antipodal reduction also guides the upper-bound search. Suppose a target is strictly sign-represented by

$$ Q(z)=t(1-b(z)^2)+u(z)v(z), $$

where $b,u,v$ are homogeneous linear forms, every coefficient of $b$ is positive, and their sum is less than one. Choose a sufficiently small positive rational $\delta$ so that $d=b+\delta v$ still has positive coefficients summing to less than one. Set

$$ U=\frac{u}{\delta}, \qquad V=-U-t(b+d). $$

Then direct multiplication gives

$$ \left(t+\frac{U}{1+b}+\frac{V}{1+d}\right)(1+b)(1+d)=t(1-b^2)+uv=Q. $$

Both denominators are positive on the sign cube and have one common slope orientation after conversion to bit coordinates. Thus this is a valid two-head representation.

The archived witnesses use integer vectors $B,U_0,V_0$, a positive integer scale $s$, and a positive integer $K$, with

$$ b(z)=\frac{B\cdot z}{s}, \qquad u(z)=\frac{U_0\cdot z}{s}, \qquad v(z)=\frac{V_0\cdot z}{s}, \qquad \delta=\frac{1}{K}, \qquad t=1. $$

The verifier checks positivity of the coefficients of $B$ and $KB+V_0$, the two strict coefficient-sum bounds, and the cleared identity at every vertex. The signed quadratic margins before multiplying by $K$ are $6858$ and $7619$, respectively. This search-based construction is converted to an exact finite proof; no floating-point sign decisions enter verification.

## A concrete coefficient-space slice

Set $b=c=1$ and retain the sorted range $a\geq1$, $0\leq d\leq1$. Away from signed-sum ties, the chamber conditions reduce to

$$ \begin{aligned} a\gt2+d &: \quad H^{\ast}=2, \cr 2-d\lt a\lt2+d &: \quad H^{\ast}=3, \cr 1\leq a\lt2-d &: \quad H^{\ast}=2. \end{aligned} $$

For fixed positive $d$, the three-head interval has width $2d$. It collapses as the fourth coefficient tends to zero. At $d=0$, every nonvanishing member of this family uses two heads. This gives both a precise degeneration of the rank obstruction and matching head constructions on either side.

In particular, with $b=c=d=1$, the path $a\gt1$ is completely settled away from $a=3$:

$$ 1\lt a\lt3 \quad\Longrightarrow\quad H^{\ast}=3, \qquad a\gt3 \quad\Longrightarrow\quad H^{\ast}=2. $$

## Verification

Run the independent standard-library verifier:

```text
python3 artifact/calculations/tdeg-2-polynomials/verify_weighted_pair_phase_diagram.py
```

It verifies all six integer certificates on $1152$ vertices, checks the weighted-antipodal identity in exact rational arithmetic, and regression-checks the analytic chamber classification on all sorted nonvanishing integer tuples with weights from zero through twelve and all coefficient sign patterns. The finite grid and sampled identity checks supplement the analytic proofs; they do not replace them.

The classification is complete for the requested nonvanishing sign functions.
