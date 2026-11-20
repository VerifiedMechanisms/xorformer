# Definition 1.9. Linear threshold functions

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. The function $f$ is a **linear threshold function** if there exist $\beta_0\in\mathbb{R}$ and $\beta\in\mathbb{R}^n$ such that the affine [score](02_score.md) $\ell$ given by

$$ \ell(x)=\beta_0+\beta^\top x $$

[classifies](03_classification.md) $f$.

The coefficient vector $\beta$ may vanish, so constant functions are included: $\beta_0=1$ gives the constant-one function, and $\beta_0=-1$ gives the constant-zero function.
