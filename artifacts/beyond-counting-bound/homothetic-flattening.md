# Flattening Denominators Can Lose a Strict Sign Pattern

## Statement and scope

There is a Boolean function on four bits with a strict two-head representation using the positive denominator slopes

$$ b_1=(1,1,1,1),\qquad b_2=(1,2,3,4), $$

but no strict two-head representation with these directions and denominators $1+b_h\cdot x/100$, even with completely unrestricted affine numerators and readout bias. The same obstruction holds for all sufficiently small positive flattening parameters. The function is not a linear threshold function, so its original two-head representation is minimal.

This refutes a particular deformation mechanism. It does not exclude deformations that change the denominator directions, and it proves neither asymptotic target for unrestricted head complexity.

## The original representation

Index cube inputs by $j=\sum_{i=0}^3 2^i x_i$. Put $u=x_0+x_1+x_2+x_3$ and $v=x_0+2x_1+3x_2+4x_3$. Define

$$ S(x)=10+\frac{71x_0+117x_1-224x_2+401x_3}{1+u}+\frac{-20x_0-259x_1+397x_2-1000x_3}{1+v}. $$

Its sixteen values, in the stated order, are

$$ \left(10,\frac{71}{2},-\frac{107}{6},\frac{35}{12},-\frac{11}{4},\frac{172}{5},-\frac83,\frac{125}{7},\frac{21}{2},-\frac83,\frac{59}{21},-\frac{21}{8},-\frac{51}{8},\frac{25}{9},-\frac{27}{10},\frac{31}{11}\right). $$

Let $y(x)=\mathrm{sign}(S(x))$. Every value is nonzero. Both denominators have positive constant and strictly positive slopes, so the manuscript's exact normal form realizes this score with two heads.

## A dual certificate for the limiting space

Write $d=v-u=x_1+2x_2+3x_3$. Consider the nine-dimensional candidate limit space

$$ K_0=\mathrm{span}\lbrace 1,x_i,x_i d:0\leq i\leq3\rbrace. $$

The following strictly positive integer vector is indexed by the same sixteen inputs:

$$ \lambda=(1,1,3,1,3,1,1,3,5,7,5,3,1,3,3,1). $$

Direct exact summation gives

$$ \sum_x\lambda_x y(x)=0,\qquad \sum_x\lambda_xy(x)x_i=0,\qquad \sum_x\lambda_xy(x)x_i d(x)=0\quad(0\leq i\leq3). $$

Consequently no element of $K_0$ has the strict signs $y$: otherwise its product with $\lambda_x y(x)$ would have strictly positive sum, contrary to these identities. In particular, no affine function has those signs. The zero-and-one-head theorem in the manuscript therefore proves that the displayed original representation has minimum head count two.

The rows $0,1,2,3,4,6,8,10,12$ of the evaluation matrix with columns $1,x_i,x_i d$ have determinant $12$. Thus the dimension is exactly nine. The certificate records an exact inverse, checked in Lean.

## An explicit flattened obstruction

For a positive real $m$, the full fixed-denominator space for $m+u$ and $m+v$ is

$$ U_m=\mathrm{span}\lbrace1,x_i/(m+u),x_i/(m+v):0\leq i\leq3\rbrace. $$

This includes arbitrary affine numerators. Indeed, if $A=a_0+\sum_i a_i x_i$ and $D=m+\sum_i b_i x_i$, then

$$ \frac{A}{D}=\frac{a_0}{m}+\sum_i\left(a_i-\frac{a_0b_i}{m}\right)\frac{x_i}{D}. $$

Multiplying every row by the positive product $(m+u)(m+v)$ shows that the strict signs available in $U_m$ are exactly those available in

$$ K_m=\mathrm{span}\lbrace(m+u)(m+v),x_i(m+v),x_i(v-u):0\leq i\leq3\rbrace. $$

At $m=100$, put

$$ \mu=(47535753,47535753,142736747,47535753,151161341,47535753,47535753,148353143,273746053,352830671,207256959,124143247,47535753,136436759,137486757,47535753). $$

All entries are positive, and exact summation gives

$$ \sum_x\mu_xy(x)(100+u(x))(100+v(x))=0,\qquad \sum_x\mu_xy(x)x_i(100+v(x))=0,\qquad \sum_x\mu_xy(x)x_i(v(x)-u(x))=0. $$

The same positive-dual argument excludes $y$ from $K_{100}$ and therefore from $U_{100}$. Dividing each denominator by $100$ does not change its numerator space. This proves the claimed failure at flattening parameter $1/100$ with arbitrary affine numerators.

## Why the obstruction persists near zero

For $t\gt0$, a column basis of the two-head space with denominators $1+tu$ and $1+tv$ is

$$ 1,\qquad\frac{x_i}{1+tu},\qquad\frac{x_i(v-u)}{(1+tu)(1+tv)}. $$

The third column group is the difference of the two original column groups divided by $t$. This basis extends continuously to the displayed basis of $K_0$ at zero. Its selected nine-row minor remains invertible near zero.

Let $A(t)$ denote this continuous evaluation matrix and set $z_x=\lambda_x y(x)$. Let $J$ be the selected nine rows, and let $I_J$ insert a nine-vector into those coordinates of a sixteen-vector. Define

$$ z(t)=z-I_J\bigl(A_J(t)^\top\bigr)^{-1}A(t)^\top z. $$

Then $A(t)^\top z(t)=0$ identically, and $z(t)\to z$ because $A(0)^\top z=0$. Every $z_x$ has the strict sign $y(x)$. By continuity and finiteness, $z_x(t)y(x)\gt0$ for every input and every sufficiently small positive $t$. This supplies a positive dual certificate throughout that interval, not merely at the limiting matrix. $\blacksquare$

## Verification and remaining gap

`verify_homothetic_flattening.py` replays every displayed score and annihilation identity with exact rational arithmetic and checks the selected matrix inverse. `HeadComplexity.HomotheticFlattening` contains eleven Lean declarations, including the strict signs, positive certificates, inverse identity, a general positive-certificate exclusion theorem, and exclusion from the flattened and limiting spaces for arbitrary real column coefficients.

The absorption identity for affine numerators, application of the manuscript's normal form, and continuity argument are complete written proofs. They are not additional end-to-end Lean declarations. No model definitions were changed.

A proof that first replaces all target-dependent denominators by their fixed-direction constant-denominator jet limits cannot use that replacement without further justification. The example disproves its unrestricted validity even at minimum head count. Allowing the directions themselves to adapt is a different question; no sign-preserving path theorem or global counting bound is proved here.
