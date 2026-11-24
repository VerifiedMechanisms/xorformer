# The Twelve-Bit Matching Obstruction Also Excludes Three Pure Rotary Heads

## Statement

For sign inputs $z_i=2x_i-1$ on twelve bits, define

$$ g(z)=1\quad\Longleftrightarrow\quad22+20\sum_{i=0}^{5}z_{2i}z_{2i+1}-\left(\sum_{i=0}^{11}z_i\right)^2\gt0. $$

In the unchanged models of [Theorem 14](014_rope_head_complexity.md),

$$ H_P(g)=H_V(g)=4. $$

The threshold degree is two. The displayed quadratic supplies the upper bound, and an off-matching two-bit face is XOR. This function therefore does not separate pure rotary attention from vanilla attention, even though its vanilla three-head lower bound uses denominator orientation.

The vanilla four-head certificate and the predicate were previously established in [run 2c00c9dca8bf, Theorem 214](https://github.com/VerifiedMechanisms/xorformer-runs/blob/1899d884da3affbf21a8528bcb74b409c9783876/theorems/06_strict_separations/214_twelve_bit_exact_four_heads.md). The new result is the pure three-head impossibility proof. The prior integer upper certificate is imported and checked again in this checkout.

## Proof

### Lemma 1. Evenization retains the pure numerator relation

Normalize the three positive denominators in centered coordinates. As in Theorem 15, write the score as

$$ F(z)=T+\sum_{h=0}^{2}\frac{u_h\cdot z}{1+\beta_h\cdot z},\qquad u_h=k_hs_h+\ell_h\beta_h,\qquad s_{hi}\gt|\beta_{hi}|. $$

The denominator normalization and numerator relation hold for every pure atom, including equal token values, where $k_h=0$. In particular every entry of $s_h$ is strictly positive.

Clear the three positive denominators to obtain a cubic polynomial $P$. The function $g$ is invariant under global complementation. Thus the even part $Q(z)=(P(z)+P(-z))/2$ has the same Boolean signs as $g$. Positive labels remain strict; nonpositive labels remain nonpositive, which is sufficient below.

Set $\lambda_h=\ell_h+T/2$. Direct expansion gives

$$ Q(z)=T+\sum_{h=0}^{2}\left(k_hs_h\cdot z+\lambda_h\beta_h\cdot z\right)\left(\sum_{j\neq h}\beta_j\cdot z\right). $$

No global assumption about denominator slope orientation is made here.

### Lemma 2. The labels force a matrix with an order-preserving inverse

Partition the coordinates into the six even positions $X$ and the six odd positions $Y$. Let $C$ be the six-by-six matrix of mixed coefficients of $Q$.

At the all-equal corner, the defining integer score is $-2$. Flipping one coordinate gives $2$, and flipping two coordinates in distinct matched pairs gives $-2$. Each off-matching cross face is therefore XOR. Its four-point difference forces

$$ C_{ij}\lt0\qquad(i\neq j). $$

Fix $X$ at the corner. Write $p_0$ for the corner value of $Q$, $p_j$ for the value after flipping $Y_j$, and $p_{jk}$ for the value after flipping distinct $Y_j,Y_k$. Every homogeneous quadratic satisfies

$$ 4\sum_iC_{ij}=3p_j-3p_0+\sum_{k\neq j}(p_k-p_{jk}). $$

The labels imply $p_j\gt0$, $p_0\leq0$, and $p_{jk}\leq0$. Consequently every column sum of $C$ is strictly positive.

Put $M=C^\top$. Its off-diagonal entries are nonpositive and its row sums are strictly positive. The elementary maximum principle implies that $M$ is invertible and that the unique solution to $Mv=w$ is strictly positive whenever $w$ is strictly positive.

**Reason.** If $Mv\leq0$ and $v_i$ is a positive maximum coordinate, then

$$ (Mv)_i=\left(\sum_jM_{ij}\right)v_i+\sum_jM_{ij}(v_j-v_i)\gt0, $$

a contradiction. Apply this first to a kernel vector and its negative, then to $-v$ when $Mv=w\gt0$. A zero coordinate of a nonnegative solution would give a nonpositive coordinate of $Mv$. This proves the strict positivity assertion.

### Lemma 3. Pure coefficients cannot produce this matrix

Let $S_X,B_X,S_Y,B_Y$ be the six-by-three matrices whose columns are the restrictions of $s_h,\beta_h$ to the two blocks. Set

$$ X=(S_X\ B_X),\qquad Y=(S_Y\ B_Y),\qquad R=J-I,\qquad K=\mathrm{diag}(k_0,k_1,k_2), $$

where $J$ is the three-by-three all-ones matrix. Let $L$ have zero diagonal and off-diagonal entries $L_{ij}=\lambda_i+\lambda_j$. Lemma 1 gives

$$ C=XHY^\top,\qquad H=\begin{pmatrix}0&KR\cr RK&L\end{pmatrix}. $$

Since $C$ is invertible, so are $X,Y,H$. The invertibility of $H$ forces every $k_h\neq0$. Because $M=YHX^\top$,

$$ H^{-1}=X^\top M^{-1}Y. $$

The upper-left three-by-three block is $S_X^\top M^{-1}S_Y$. Every entry is strictly positive by Lemma 2 and the positivity of all entries of $S_X,S_Y$.

On the other hand, using $R^{-1}=-I+J/2$, direct inversion gives the entries of that block:

$$ (H^{-1})_{ii}=\frac{\lambda_i}{k_i^2},\qquad (H^{-1})_{ij}=-\frac{\lambda_i+\lambda_j}{2k_ik_j}\quad(i\neq j). $$

Positive diagonal entries imply every $\lambda_i\gt0$. Positive off-diagonal entries then imply $k_ik_j\lt0$ for all three pairs. Three nonzero real numbers cannot have all three pairwise products negative. This is a contradiction.

The Lean proof uses three positive solutions of $Mv=S_{Y,j}$ and an explicit coefficient-map inverse instead of an abstract matrix inverse. It proves the same conclusion without assuming nonzero token-value differences in advance.

### Lemma 4. Four heads suffice exactly

The [four-head integer certificate](../../artifacts/rope/prior_obstructions/twelve_pair_four_heads.json) stores affine numerator and denominator rows in Boolean coordinates. Every denominator slope is negative. Their minimum values on the cube are $325,324,301,324$. The cleared integer score has the desired sign at all $4096$ inputs, with minimum absolute value $13096942950$.

Each ratio is vanilla-admissible. The exact affine-fraction realization theorem supplies a shared-embedding vanilla architecture with four heads. Theorem 14 then supplies four pure rotary heads. The [rational pure atom certificate](../../artifacts/rope/prior_obstructions/twelve_pair_pure_four_heads.json) applies that conversion explicitly: its numerator and denominator coefficients agree exactly with the four integer fractions.

Lemmas 1 through 3 exclude three pure heads and therefore every smaller pure budget by zero-head padding. Since pure rotary complexity is at most vanilla complexity, Lemma 4 proves both counts are four. $\blacksquare$

## Formalization and certificate verification

All new declarations use the existing definitions and permit unrestricted finite width and arbitrary real parameters.

- [PureRoPEThreeHeadCross.lean](../../formalization/HeadComplexity/Polynomial/PureRoPEThreeHeadCross.lean): `PureRoPEThreeHeadCross.obstruction` proves the general six-direction matrix obstruction. `transform_inverse`, `inverseA_not_positive`, and `evenization` check the central identities.

- [PureRoPEThreeHeadObstruction.lean](../../formalization/HeadComplexity/Results/PureRoPEThreeHeadObstruction.lean): `PureRoPEThreeHead.exists_quadratic` derives the necessary form from actual pure atoms. In namespace `PureRoPEThreeHead.TwelvePair`, `not_pureRoPEComputable_three` and `pureRoPEHStar_ge_four` prove the full scalar lower bound.

- [PureRoPETwelvePairExact.lean](../../formalization/HeadComplexity/Results/PureRoPETwelvePairExact.lean): in the same namespace, `integer_certificate`, `vanillaHStar_eq_four`, `pureRoPEHStar_eq_four`, and `sharedHStar_eq_four` check the upper certificate and exact counts. `thresholdDeg_eq_two` checks the threshold degree, and `exact_complexities` combines the three scalar complexities.

- [verify_twelve_pair.py](../../artifacts/rope/prior_obstructions/verify_twelve_pair.py) checks all classifications with Python integers and checks the rational pure conversion coefficient by coefficient.

The vanilla shared-embedding bridge is part of the Lean theorem. The pure scalar-to-architecture bridge remains the fixed-frequency interpolation construction in Theorem 14. Thus the new Lean statements concern the unchanged scalar pure model, with their architectural interpretation supplied by that existing proof.
