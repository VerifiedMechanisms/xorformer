# Normalized Energy Can Diverge Under Two-Head Cancellation

## Statement

The single-head elliptic potential bound does not extend to a uniform bound for the corresponding block operator on sums of two heads. This fails even for a fixed Boolean function of head complexity exactly two, with every denominator coefficient strictly positive.

For $0\lt t\leq1$ and $(x,y)\in\lbrace0,1\rbrace^2$, put

$$ A=x-\tfrac12,\qquad B=y-\tfrac12,\qquad D=1+x+y,\qquad S_t=\frac{A}{D}-\frac{A}{D+tB}=\frac{tAB}{D(D+tB)}. $$

Normalize the entire four-entry score table by $U_t=S_t/\|S_t\|_2$. Consider the natural block elliptic operator obtained by allowing the two normalized denominator slope vectors to vary independently, while holding their affine numerators fixed. Its normalized potential $V_t$ satisfies

$$ V_t\geq\frac{1}{1024t^2}. $$

Consequently $V_t$ is unbounded as $t$ decreases to zero. In particular there is no bound $V\leq C H$, with a universal constant $C$, for all admissible $H$-head representations, even if their head count is minimal for their Boolean function.

This is a statement about this specified parameter operator. It is not an assertion that every possible representation of the function has large potential, or that an intrinsic metric on the table image must have large energy. It proves no worst-case head lower bound.

## Admissibility and the fixed Boolean function

The second denominator is

$$ D+tB=(1-t/2)+x+(1+t)y. $$

Its constant is at least one half and both slopes are positive. The first denominator has positive constant and slopes as well. Both numerators are affine. Thus these are admissible heads for every parameter in the stated interval.

The score has the sign of $AB$. It is positive at $00$ and $11$ and negative at $10$ and $01$. This Boolean function is not an affine threshold: an affine score would satisfy

$$ F(00)+F(11)=F(10)+F(01), $$

contradicting these four strict signs. One head, including its free output bias, has an affine numerator after multiplying by its positive denominator. Strictification therefore excludes a one-head representation. The displayed two-head representation proves that the head complexity is exactly two.

## The block elliptic identity

For clarity, the construction is put in the constant-one denominator coordinates used by the elliptic identity. For fixed $t$, set $c=1-t/2$. The slope vectors and numerators at the point in question are

$$ b^{(1)}=(1,1),\qquad b^{(2)}=(1/c,(1+t)/c),\qquad a^{(1)}=A,\qquad a^{(2)}=-A/c. $$

Each head now has denominator $1+b^{(h)}\cdot(x,y)$. When differentiating the model, these two numerator tables are held fixed and the two slope vectors are independent variables. This is not differentiation along the one-dimensional path $t\mapsto S_t$.

Write $M_h=\mathrm{diag}(b^{(h)})+b^{(h)}(b^{(h)})^\top$. The unnormalized score satisfies

$$ \mathcal L S=0,\qquad \mathcal L=\sum_{h=1}^2\left(M_h:\nabla_h^2+2(b^{(h)})^\top\nabla_h\right). $$

Indeed each block annihilates its own head by the [single-head calculation](head-elliptic-energy.md), and every other head is constant in that block. Every $M_h$ is positive definite.

For $\rho=\|S\|_2$ and $U=S/\rho$, the product rule gives the normalized equation

$$ \mathcal L U+2\sum_h(\nabla_h\log\rho)^\top M_h\nabla_h U+VU=0,\qquad V=\sum_z\sum_h(\nabla_h U_z)^\top M_h\nabla_h U_z=\frac{\mathcal L\rho}{\rho}. $$

Here $z$ runs through the four cube vertices. The equality for $V$ follows by differentiating $\rho^2=\sum_zS_z^2$, using $\mathcal LS_z=0$, and applying the chain rule to the square root. Thus the same normalized equation survives, but its potential need not retain the single-head upper bound.

## Exact energy lower bound

Order the vertices as $00,10,01,11$, and write the score entries as $s_0,s_1,s_2,s_3$. Direct simplification gives

$$ s_0=\frac{t}{4-2t},\qquad s_1=-\frac{t}{16-4t},\qquad s_2=-\frac{t}{16+4t},\qquad s_3=\frac{t}{36+6t}. $$

All four denominators are positive. The displayed formulas imply

$$ s_0\geq\frac t4,\qquad |s_i|\leq\frac t2\quad(0\leq i\leq3),\qquad 0\lt G:=\sum_i s_i^2\leq t^2. $$

Differentiate in the first head's first denominator slope. The derivative vector of the unnormalized score is

$$ g=\partial_{b^{(1)}_1}S=(0,-1/8,0,-1/18). $$

Differentiating $U=S/\sqrt G$ therefore gives

$$ \left\|\partial_{b^{(1)}_1}U\right\|_2^2=\frac{G\|g\|_2^2-\langle S,g\rangle^2}{G^2}. $$

The numerator is a sum of squared two-coordinate minors, with the following explicit identity:

$$ G\|g\|_2^2-\langle S,g\rangle^2=(s_0/8)^2+(s_0/18)^2+(s_2/8)^2+(s_1/18-s_3/8)^2+(s_2/18)^2\geq\frac{t^2}{1024}. $$

Since $G^2\leq t^4$, this proves

$$ \left\|\partial_{b^{(1)}_1}U\right\|_2^2\geq\frac{1}{1024t^2}. $$

The first block matrix has diagonal entries two and off-diagonal entries one. For real $v,w$,

$$ (v,w)M_1(v,w)^\top=v^2+(v+w)^2+w^2\geq v^2. $$

The second block is positive definite. Summing over vertices therefore gives $V_t\geq\|\partial_{b^{(1)}_1}U\|_2^2$, proving the claimed bound. For an explicit unboundedness witness, given $C\geq0$ choose $t=1/(1024(C+1))$. Then the lower bound is $1024(C+1)^2\gt C$. $\blacksquare$

## Consequence and verification scope

This example retains affine numerators and uses two heads that are necessary for the fixed sign pattern. It therefore supplies a different obstruction from allowing arbitrary numerator tables. A uniformly bounded potential for the independent denominator blocks cannot be used to extend the single-head identity. A selection theorem producing different representations with controlled potential would be a new, presently unproved ingredient.

`formalization/HeadComplexity/Atoms/CancellationEnergy.lean` proves the two-head rational identity, exact four-entry table, admissibility inequalities, strict signs, affine obstruction, squared-minor identity, norm estimates, and unbounded angular energy. In particular, `HeadComplexity.CancellationEnergy.angularEnergy_lower` and `HeadComplexity.CancellationEnergy.angularEnergy_unbounded` are general real-variable declarations. The differential interpretation and full block-operator statement are the complete written calculation above, not a claimed Lean calculus theorem.

`verify_cancellation_energy.py` independently evaluates first and second derivatives of both normalized-denominator heads with exact rational arithmetic. It checks the full normalized block equation after multiplication by the positive table norm, as well as the lower bound. These finite checks do not replace the general proof or imply the research target.
