# Linear-Fractional Normal Form

## Statement

In the Boolean-input model from [../../model.md](../../model.md), the scalar scores realizable with $H$ heads are **exactly** the functions

$$ \Phi(x)=c+\sum_{h=1}^{H}\frac{A_h^\top x+b_h}{C_h^\top x+d_h}, \qquad x\in\lbrace0,1\rbrace^n, $$

The constant $c$ and the numerator constants $b_h$ are arbitrary. For each head:

1. The denominator $C_h^\top x+d_h$ is strictly positive throughout the Boolean cube.
2. The entries of $C_h$ are all strictly positive, all strictly negative, or all zero.

The numerator is arbitrary when the denominator is nonconstant. If $C_h=0$, the entries of $A_h$ must also be all strictly positive, all strictly negative, or all zero. Call such coefficient tuples *admissible*.

The correspondence preserves the entire real-valued score before thresholding, with shared token and positional embeddings and unrestricted model width. The constant $c$ absorbs the readout threshold and the constant query residual.

For $H=0$, the sum is empty and $\Phi(x)=c$. For $n=0$, admissibility reduces to $d_h\gt0$.

Consequently, if $L_{\mathrm{aff}}(f)$ denotes the least number of admissible ratios in a score with $f(x)=1$ exactly when $\Phi(x)\gt0$, then

$$ H^{\ast}(f)=L_{\mathrm{frac}}(f)=L_{\mathrm{aff}}(f). $$

Here $L_{\mathrm{frac}}$ is the equivalent atom count defined below.

> **Scope.** Admissibility characterizes coefficients obtained by expanding individual heads. A cube function may have several ratio representations, so an inadmissible tuple does not rule out another admissible representation of that function.

### Equivalent atom form

For parameters

$$ \gamma \gt 0, \qquad \rho_1, \ldots, \rho_n \gt 0, \qquad \alpha \gt 0, $$

and

$$ \eta, \delta, m_1, \ldots, m_n \in \mathbb{R}, $$

define a one-head atom

$$ \phi(x) := \frac{ \eta + \sum_{i=1}^{n} \rho_i \alpha^{x_i}(m_i + \delta x_i) }{ \gamma + \sum_{i=1}^{n} \rho_i \alpha^{x_i} }. $$

Here $x_i \in \lbrace0,1\rbrace$, so $\alpha^{x_i}$ means $1$ when $x_i = 0$ and $\alpha$ when $x_i = 1$.

Define $L_{\mathrm{frac}}(f)$ to be the least $H$ such that there exist one-head atoms

$$ \phi_1, \ldots, \phi_H $$

and a constant $c \in \mathbb{R}$ with

$$ f(x) = 1 \qquad \Longleftrightarrow \qquad c + \sum_{h=1}^{H} \phi_h(x) \gt 0 $$

for every $x \in \lbrace0,1\rbrace^n$. For $H = 0$, the sum is empty.

The atom and affine-ratio forms agree under the coefficient map

$$ A_{h,i}=\rho_{h,i}\bigl((\alpha_h-1)m_{h,i}+\alpha_h\delta_h\bigr), \qquad b_h=\eta_h+\sum_i\rho_{h,i}m_{h,i}, $$

$$ C_{h,i}=\rho_{h,i}(\alpha_h-1), \qquad d_h=\gamma_h+\sum_i\rho_{h,i}. $$

A prescribed coefficient tuple is obtained by this map **if and only if** it is admissible.

> **Interpretation.** Head complexity is the minimum number of admissible affine ratios whose sum, plus a constant, sign-represents $f$. The first two levels are pinned down in [011_one_head_characterization.md](011_one_head_characterization.md).

## Proof

We prove the head-to-atom correspondence in both directions, then characterize the coefficients of each atom exactly.

### Theorem 1. Every attention head gives one atom

Fix an $H$-head model and a final readout vector $w$ with threshold $\tau$.

For head $h$, write

$$ q_h := W_Q^{(h)} u_=. $$

This vector is constant as a function of the input $x$.

For each input position $i$, define

$$ \rho_{h,i} := \exp \left( \left\langle q_h, W_K^{(h)}(e_0 + p_i) \right\rangle \right) \gt 0, $$

and

$$ \alpha_h := \exp \left( \left\langle q_h, W_K^{(h)}(e_1 - e_0) \right\rangle \right) \gt 0. $$

Then the unnormalized attention weight assigned by head $h$ to input position $i$ is

$$ \rho_{h,i} \alpha_h^{x_i}. $$

Now define the scalar value seen by the final readout. For each input position $i$, set

$$ m_{h,i} := \left\langle w, W_O^{(h)} W_V^{(h)}(e_0 + p_i) \right\rangle, $$

and

$$ \delta_h := \left\langle w, W_O^{(h)} W_V^{(h)}(e_1 - e_0) \right\rangle. $$

So the scalar value contribution at position $i$ is

$$ m_{h,i} + \delta_h x_i. $$

For the query token itself, define

$$ \gamma_h := \exp \left( \left\langle q_h, W_K^{(h)} u_= \right\rangle \right) \gt 0, $$

and

$$ \eta_h := \gamma_h \left\langle w, W_O^{(h)} W_V^{(h)} u_= \right\rangle. $$

Therefore the scalar contribution of head $h$ to the final readout is exactly

$$ \phi_h(x) = \frac{ \eta_h + \sum_{i=1}^{n} \rho_{h,i} \alpha_h^{x_i}(m_{h,i} + \delta_h x_i) }{ \gamma_h + \sum_{i=1}^{n} \rho_{h,i} \alpha_h^{x_i} }. $$

This is a one-head atom.

The full affine score of the model is

$$ w^\top r(x) - \tau = c + \sum_{h=1}^{H} \phi_h(x), $$

where

$$ c := w^\top u_= - \tau. $$

Thus every $H$-head model gives an $H$-atom representation.

### Theorem 2. Every atom is realized by one attention head

Now suppose we are given $H$ atoms. We construct an $H$-head model realizing their sum.

If $H = 0$, choose $w=0$ and $\tau=-c$ to realize the constant score $c$ exactly. So assume $H \geq 1$.

For each head $h$, take an independent block with orthonormal basis

$$ q_h, k_h, v_h, o_h. $$

Use the direct sum of all these blocks as the model space, and take $d_{\mathrm{head}} = d_{\mathrm{model}}$.

Define token embeddings by

$$ e_0 := 0, $$

$$ e_1 := \sum_{h=1}^{H} \bigl((\log \alpha_h) k_h + \delta_h v_h\bigr), $$

and

$$ e_= := \sum_{h=1}^{H} \left( q_h + (\log \gamma_h) k_h + \frac{\eta_h}{\gamma_h} v_h \right). $$

For input position $i$, set

$$ p_i := \sum_{h=1}^{H} \bigl((\log \rho_{h,i}) k_h + m_{h,i} v_h\bigr), $$

and set $p_= := 0$.

For head $h$, choose linear maps as follows.

1. $W_Q^{(h)}$ sends $q_h$ to $q_h$ and annihilates every other basis vector.
2. $W_K^{(h)}$ sends $k_h$ to $q_h$ and annihilates every other basis vector.
3. $W_V^{(h)}$ sends $v_h$ to $o_h$ and annihilates every other basis vector.
4. $W_O^{(h)}$ fixes $o_h$ and annihilates every other basis vector.

Then the query vector for head $h$ is $q_h$.

At input position $i$, the logit is

$$ \log \rho_{h,i} + x_i \log \alpha_h, $$

so the unnormalized attention weight is

$$ \rho_{h,i} \alpha_h^{x_i}. $$

The value written in the $o_h$ direction at that position is

$$ m_{h,i} + \delta_h x_i. $$

At the query token, the logit is $\log \gamma_h$, the unnormalized attention weight is $\gamma_h$, and the value written in the $o_h$ direction is $\eta_h / \gamma_h$.

Therefore the projected output of head $h$ is exactly

$$ \phi_h(x)   o_h. $$

Choose the final readout vector

$$ w := \sum_{h=1}^{H} o_h $$

and choose threshold

$$ \tau := -c. $$

The skip connection at the query token is orthogonal to every $o_h$, so it contributes nothing to $w^\top r(x)$. Hence

$$ w^\top r(x) - \tau = c + \sum_{h=1}^{H} \phi_h(x). $$

So the model realizes the entire score represented by the atoms.

### Theorem 3. Exact affine coefficients

Suppress the head index and consider a single atom.

**Expansion and necessity.** For a bit $x_i$, we have

$$ \alpha^{x_i}=1+(\alpha-1)x_i, \qquad \alpha^{x_i}(m_i+\delta x_i)=m_i+\bigl((\alpha-1)m_i+\alpha\delta\bigr)x_i. $$

Expanding the numerator and denominator separately gives the coefficient map. Since $\gamma,\rho_i,\alpha\gt0$, we have $d\gt0$. The cases $\alpha\gt1$ and $\alpha\lt1$ give the two strict orientations of $C$. In the latter case,

$$ d+\sum_i C_i=\gamma+\alpha\sum_i\rho_i\gt0. $$

When $\alpha=1$, we have $C_i=0$ and $A_i=\rho_i\delta$, so the numerator slopes share the sign of $\delta$.

**Constructive converse.** Fix a prescribed admissible tuple $(A,b,C,d)$.

Denominator positivity gives $d\gt0$ by evaluating at the all-zero input. If every $C_i\lt0$, evaluating at the all-one input also gives $d+\sum_i C_i\gt0$. Conversely, under the sign condition on $C$, these inequalities ensure positivity throughout the cube. We use them to construct the atom below.

**Nonconstant denominator.** In either strict orientation, use the same inverse formulas:

$$ \rho_i=\frac{C_i}{\alpha-1}, \qquad \gamma=d-\sum_i\rho_i, \qquad \delta=0, \qquad m_i=\frac{A_i}{C_i}, \qquad \eta=b-\sum_i\rho_i m_i. $$

It remains to choose $\alpha$ so that $\alpha,\rho_i,\gamma\gt0$.

For positive slopes, put $S=\sum_i C_i$ and $\alpha=2+S/d$. Then every $\rho_i\gt0$ and $\sum_i\rho_i=S/(1+S/d)\lt d$.

For negative slopes, put $S=-\sum_i C_i$ and $\alpha=(d-S)/(2d)$. The hypothesis gives $0\leq S\lt d$, hence $0\lt\alpha\lt1$. Every $\rho_i\gt0$, and $\sum_i\rho_i=2dS/(d+S)\lt d$.

Thus both constructions have $\gamma\gt0$ and produce the prescribed coefficients exactly.

**Constant denominator.** Set $\alpha=1$. If the numerator slopes share a strict sign, choose $\sigma\in\lbrace-1,1\rbrace$ with $v_i=\sigma A_i\gt0$, and set

$$ q=1+\frac{\sum_i v_i}{d}, \qquad \rho_i=\frac{v_i}{q}, \qquad \delta=\sigma q, \qquad m_i=0, \qquad \eta=b, \qquad \gamma=d-\sum_i\rho_i. $$

Then $\rho_i\delta=A_i$, every $\rho_i\gt0$, and $\sum_i\rho_i\lt d$.

If $A=C=0$, choose $\delta=0$, $m_i=0$, $\eta=b$, and $\rho_i=\gamma=d/(n+1)$. All required weights are positive and the coefficients are exact. This also covers $n=0$: there are no position weights, and $\gamma=d$, $\eta=b$.

Every admissible denominator is therefore an atom denominator, which is strictly positive on the Boolean cube.

### Combining the two directions

The head-to-atom constructions preserve the exact score and the number of heads. The coefficient characterization above shows that expanding each atom gives an admissible affine ratio, and every prescribed admissible tuple comes from an atom. Substituting these identities term by term gives precisely

$$ \Phi(x)=c+\sum_{h=1}^{H}\frac{A_h^\top x+b_h}{C_h^\top x+d_h} $$

in both directions. Thresholding at zero and minimizing the number of terms yields

$$ H^{\ast}(f)=L_{\mathrm{frac}}(f)=L_{\mathrm{aff}}(f). \qquad \blacksquare $$

## Different representations and strict boundaries

The tuple with numerator $x_1-x_2$ and denominator $1$ is inadmissible because its numerator slopes have opposite signs. Nevertheless,

$$ x_1-x_2=\frac{2x_1-2x_2}{1+x_1+x_2}, \qquad (x_1,x_2)\in\lbrace0,1\rbrace^2. $$

The tuple on the right is admissible. The identity follows from $x_i^2=x_i$, so this score is exactly realizable by one atom.

Denominator positivity alone is insufficient. The positive denominator $3+x_1-x_2$ has mixed slopes, and $1+x_1$ in two dimensions has partially zero slopes. Neither is an expanded atom denominator. The boundary denominator $2-x_1-x_2$ is also excluded: it vanishes at the all-one vertex.

These statements concern the existing Boolean-input model. They make no claim about continuous probe inputs.

## Formalization

`Atoms/AffineFraction.lean` defines `AffineFraction.Admissible` directly by positivity on the Boolean cube, `UniformSign` for the denominator slopes, and `UniformSign` for the numerator slopes when the denominator is constant. It proves the coefficient characterization in `AffineFraction.realizable_iff`, using separate numerator and denominator expansion identities and a constructive converse. The public index exposes it as `theorem10_affine_coefficients`.

`shared_score_iff_affineFraction` in `Results/AffineFractionNormalForm.lean` proves the exact score equivalence for the shared-embedding model, including zero heads and zero inputs. `computableWithSharedHeadsN_iff_affineFractionComputable` and `SharedHStar_eq_LaffineFrac` give the thresholded and minimum-count statements. The public index exposes them as `theorem10_affine_score_normal_form`, `theorem10_affine_per_head_count`, and `theorem10_affine_complexity`.

`Examples/AffineFraction.lean` verifies all coefficient cases, dimension zero, zero-head constant scores, the strict exclusions, and the alternative representation above with an arbitrary additive constant.
