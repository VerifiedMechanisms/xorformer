# Definition 1.2. Score

For $n\in\mathbb{Z}_{\geq1}$, a **score** on $n$ input bits is a function $\Phi:\lbrace0,1\rbrace^n\to\mathbb{R}$.

For a [model](01_model.md), a readout vector $w\in\mathbb{R}^{d_{\mathrm{model}}}$ and threshold $\tau\in\mathbb{R}$ give the score $\Phi$ defined by

$$ \Phi(x)=w^\top r(x)-\tau. $$

A score $\Phi$ is **realizable with $H$ heads** if there exist positive integer model and head dimensions, model parameters, and a readout for which this equality holds on every input. Each realization may choose its own finite dimensions, with no fixed upper bound.
