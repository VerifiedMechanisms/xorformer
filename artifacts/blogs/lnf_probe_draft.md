# Getting started with the LNF Probe

[Theorem 10](https://github.com/VerifiedMechanisms/xorformer/blob/main/theorems/01_foundations_and_normal_form/010_linear_fractional_normal_form.md) has been the basis for many of the other theorems in the [autoresearch branch](https://github.com/VerifiedMechanisms/xorformer/tree/autoresearch). I initially thought we needed more theoretical progress before we could get to empirical work. Recent discussions have convinced me that it's worth trying some empirical analysis with Theorem 10 as it stands.

Its linear-fractional normal form (LNF) describes each head's contribution in our Boolean-input model and gives us a concrete set of coefficients to examine.

## Brief intro to Theorem 10

**Theorem 10 (Linear-fractional normal form).** In our one-layer, attention-only model with Boolean inputs, shared token and positional embeddings, and a linear readout at a fixed query token, the scalar scores realizable with $H$ heads are exactly

$$ \Phi(x)=c+\sum_{h=1}^{H}\frac{(A^{(h)})^\top x+b^{(h)}}{(C^{(h)})^\top x+d^{(h)}}, \qquad x\in\lbrace0,1\rbrace^n. $$

Here $A^{(h)},C^{(h)}\in\mathbb{R}^n$ and $b^{(h)},d^{(h)},c\in\mathbb{R}$. We write $\mathbf{0}\in\mathbb{R}^n$ for the zero vector.

<details>
<summary>Conditions on the LNF coefficients</summary>

For each head $h$:

1. $(C^{(h)})^\top x+d^{(h)}\gt0 \quad \forall x\in\lbrace0,1\rbrace^n$, i.e. the denominator is strictly positive throughout the Boolean cube.
2. $(\forall i, C_i^{(h)}\gt0)$, or $(\forall i, C_i^{(h)}\lt0)$, or $C^{(h)}=\mathbf{0}$, i.e. the denominator slopes are all strictly positive, all strictly negative, or all zero.
3. If $C^{(h)}=\mathbf{0}$, then $(\forall i, A_i^{(h)}\gt0)$, or $(\forall i, A_i^{(h)}\lt0)$, or $A^{(h)}=\mathbf{0}$, i.e. a constant denominator requires numerator slopes that are all strictly positive, all strictly negative, or all zero. For $C^{(h)}\neq\mathbf{0}$, the numerator is unrestricted.
4. The constants $c$ and $b^{(h)}$ are unrestricted.

</details>

On every Boolean input, $\Phi(x)$ is the model's classification score, with the query token's residual contribution and classification threshold absorbed into $c$. Conversely, every sum satisfying these conditions is realizable with $H$ heads, shared embeddings, and unrestricted model width.

These conditions describe exactly which coefficient tuples can be obtained from a head's attention weights and scalar values using the formulas below. Different coefficient tuples can represent the same function on the cube. The [proof of Theorem 10](https://github.com/VerifiedMechanisms/xorformer/blob/main/theorems/01_foundations_and_normal_form/010_linear_fractional_normal_form.md) is in the repository.

## Model weights ↔ LNF coefficients

For a given model, we can write these coefficients directly from its weights.

Let $e_0,e_1,e_=$ be the token embeddings for the two input symbols and the query token. Let $p_i$ be the positional embedding at input position $i$, and $p_=$ the query's positional embedding. Write

$$ u_i^{(t)}=e_t+p_i \quad \text{for }t\in\lbrace0,1\rbrace, \qquad u_=e_=+p_=. $$

For head $h$, let $W_Q^{(h)},W_K^{(h)},W_V^{(h)},W_O^{(h)}$ be its query, key, value, and output projection matrices. Let $w$ be the final readout vector. The query is fixed:

$$ q^{(h)}=W_Q^{(h)}u_=. $$

For any embedded token vector $u$, define:

**Attention weight (unnormalized):**

$$ s^{(h)}(u)=\exp\left((q^{(h)})^\top W_K^{(h)}u\right). $$

**Embedding readout:** the scalar value after output projection and readout.

$$ v^{(h)}(u)=w^\top W_O^{(h)}W_V^{(h)}u. $$

For $t\in\lbrace0,1\rbrace$, collect the input-token attention weights and embedding readouts into column vectors:

$$ S^{(h)}(t)=\bigl(s^{(h)}(u_i^{(t)})\bigr)_{i=1}^n, \qquad V^{(h)}(t)=\bigl(v^{(h)}(u_i^{(t)})\bigr)_{i=1}^n. $$

These vectors connect directly to the [QK and OV circuit decomposition](https://transformer-circuits.pub/2021/framework/).[^circuits] With our column-vector convention, the two circuit matrices are

$$ W_{QK}^{(h)}=(W_Q^{(h)})^\top W_K^{(h)}, \qquad W_{OV}^{(h)}=W_O^{(h)}W_V^{(h)}. $$

- $S^{(h)}(t)$ evaluates the **QK circuit** at the fixed query and each input embedding: its entries are $\exp(u_=^\top W_{QK}^{(h)}u_i^{(t)})$. These are the attention weights before normalization.
- $V^{(h)}(t)$ evaluates the **OV circuit through the final readout**: its entries are $w^\top W_{OV}^{(h)}u_i^{(t)}$. This measures the scalar signal that each input embedding would contribute if attended to.

**LNF coefficients:**

Write $\odot$ for elementwise multiplication and $\mathbf{1}\in\mathbb{R}^n$ for the all-ones vector. The coefficients of head $h$ are

$$ \boxed{A^{(h)}=S^{(h)}(1)\odot V^{(h)}(1)-S^{(h)}(0)\odot V^{(h)}(0)} $$

$$ \boxed{b^{(h)}=s^{(h)}(u_=)v^{(h)}(u_=)+S^{(h)}(0)^\top V^{(h)}(0)} $$

$$ \boxed{C^{(h)}=S^{(h)}(1)-S^{(h)}(0)} $$

$$ \boxed{d^{(h)}=s^{(h)}(u_=)+\mathbf{1}^\top S^{(h)}(0)} $$

Each coefficient has a direct interpretation, with all attention weights understood to be unnormalized:

- $A_i^{(h)}$: the response of the weighted readout $s^{(h)}v^{(h)}$ to a bit flip $x_i:0\to1$.
- $b^{(h)}$: the numerator at the all-zero input: the total weighted readout, including the query token.
- $C_i^{(h)}$: the response of the attention weight $s^{(h)}$ to the same bit flip.
- $d^{(h)}$: the denominator at the all-zero input: the total attention weight, including the query token.

At each input position, the Boolean bit selects one of two fixed embeddings. Its contribution to the numerator is therefore its bit-zero contribution plus $A_i^{(h)}x_i$, and its contribution to the denominator is its bit-zero attention weight plus $C_i^{(h)}x_i$. Summing over positions and including the query token gives exactly $(A^{(h)})^\top x+b^{(h)}$ and $(C^{(h)})^\top x+d^{(h)}$. Their ratio is the head's contribution to the classification score.

Together, these quantities determine the score $\Phi(x)$; the classifier outputs one when $\Phi(x)\gt0$.

## From QK/OV circuits to **causal** contributions

The coefficients give us two related views of a head:

1. **Attention normalization through the QK circuit.** $C^{(h)}$ and $d^{(h)}$ describe the total unnormalized attention weight and its response to input bits. For fixed embeddings and query token, they depend only on the QK circuit. They summarize its normalization behavior on this input domain; they do not specify the full QK matrix or, in general, the individual attention weights.
2. **Readout through the combined QK and OV circuits.** $A^{(h)}$ and $b^{(h)}$ describe the OV signal weighted by QK attention and projected onto the final readout. Changes to the QK circuit can therefore affect both the numerator and denominator, while changes to the OV circuit affect the numerator.

### Score changes under interventions

Each head's affine-ratio term $\phi^{(h)}(x)$ directly measures its contribution to the classification score. In this one-layer model, it equals the score difference between keeping the head and setting its output to zero with the rest of the model fixed. This gives $\phi^{(h)}(x)$ a precise **causal** interpretation under head ablation. Can patterns in the LNF coefficients help us identify what a head computes and predict when removing it will affect performance? We can test these predictions through ablation experiments.

The [QK/OV framework](https://transformer-circuits.pub/2021/framework/) already decomposes output contributions, and [circuit studies use head ablations to test **causal** hypotheses](https://transformer-circuits.pub/2022/in-context-learning-and-induction-heads/). **LNF probes use an exact description with $2n+2$ coefficients per head**, valid across the entire Boolean cube. This lets us connect patterns in the coefficients to explicit intervention effects. Whether those patterns reveal useful mechanisms remains an empirical question.

> Do useful heads have a clear signature in $A^{(h)},b^{(h)},C^{(h)},d^{(h)}$? If so, what does it look like, and can it help us identify the heads implementing the function when $H\gt H^{\ast}(f)$? This would give us a concrete starting point for an LNF probe.

## First experiments

Let's train the [model specified in model.md](https://github.com/VerifiedMechanisms/xorformer/blob/main/model.md) on small Boolean functions $f$ and analyse $A^{(h)},b^{(h)},C^{(h)},d^{(h)}$ for each learned head. Two-bit XOR, $f(x)=x_1\oplus x_2$, is one example. I would also consider nonsymmetric Boolean functions.

Here are some experiments off the top of my head.

1. **At the minimum head count.** For a function with known $H^{\ast}(f)$, train with $H=H^{\ast}(f)$ across several random seeds and check the full truth table. For runs that compute $f$ correctly, compare the signs and relative magnitudes of the coefficients and each head's contribution to the score. Do similar coefficient patterns recur across runs?
2. **Patterns in the coefficients.** Do heads show systematic relationships between their LNF coefficients? For example, does $\lvert(A^{(h)})^\top x\rvert\gg\lvert b^{(h)}\rvert$ hold for every Boolean input $x\neq\mathbf{0}$, so that the input-dependent numerator dominates its all-zero baseline? Are there similar patterns between $(C^{(h)})^\top x$ and $d^{(h)}$?
3. **More heads than necessary.** Repeat with $H\gt H^{\ast}(f)$. Use the coefficients to propose which heads are useful or redundant. Check those predictions by ablation experiments.

For comparisons across heads and runs, divide each head's four coefficients by $d^{(h)}\gt0$. This sets its denominator constant to one and removes a common scale factor without changing the head's contribution.

[^circuits]: Here, “circuit” simply means the relevant pair of projection matrices and their composition: query and key for QK, value and output for OV.
