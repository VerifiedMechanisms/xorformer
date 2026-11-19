# Definition 1.1. Model

## Inputs and parameters

Let $n\in\mathbb{Z}_{\geq1}$ and $H\in\mathbb{Z} _{\geq0}$. An input $x\in\lbrace0,1\rbrace^n$ gives the sequence of input bits followed by a designated query token, written $=$.

Choose positive integer model and head dimensions $d_{\mathrm{model}}$ and $d_{\mathrm{head}}$. The **residual space** is $\mathbb{R}^{d_{\mathrm{model}}}$. Choose token embeddings $e_0,e_1,e_{=}\in\mathbb{R}^{d_{\mathrm{model}}}$ and positional embeddings $p_1,\ldots,p_n,p_{=}\in\mathbb{R}^{d_{\mathrm{model}}}$. Define

$$ u_i(x)=e_{x_i}+p_i\quad(1\leq i\leq n), \qquad u_{=}=e_{=}+p_{=}. $$

Write $J_n=\lbrace1,\ldots,n,=\rbrace$ for the position set. All parameters are fixed independently of the input.

## Attention

For each head $h\in\lbrace1,\ldots,H\rbrace$, choose linear maps

$$ W_Q^{(h)},W_K^{(h)},W_V^{(h)}:\mathbb{R}^{d_{\mathrm{model}}}\to\mathbb{R}^{d_{\mathrm{head}}}, \qquad W_O^{(h)}:\mathbb{R}^{d_{\mathrm{head}}}\to\mathbb{R}^{d_{\mathrm{model}}}. $$

The query, keys, and values are

$$ q_h=W_Q^{(h)}u_{=}, \qquad k_{h,j}(x)=W_K^{(h)}u_j(x), \qquad v_{h,j}(x)=W_V^{(h)}u_j(x), \qquad j\in J_n, $$

where $u_{=}(x)=u_{=}$. The attention weights and projected head outputs are

$$ a_{h,j}(x)=\frac{\exp(q_h^\top k_{h,j}(x))}{\sum_{k\in J_n}\exp(q_h^\top k_{h,k}(x))}, \qquad y_h(x)=W_O^{(h)}\sum_{j\in J_n}a_{h,j}(x)v_{h,j}(x). $$

The query attends to every input position and itself. Since it is last in the sequence, these are also the positions available to it under a causal mask. A constant logit scaling factor can be absorbed into the query or key map.

## Query residual

The **query residual** $r(x)\in\mathbb{R}^{d_{\mathrm{model}}}$ is the output of the layer at the query position:

$$ r(x)=u_{=}+\sum_{h=1}^{H}y_h(x). $$

For $H=0$, the sum is empty. The architecture has one attention layer, with no MLP, layer normalization, dropout, or additional layers.
