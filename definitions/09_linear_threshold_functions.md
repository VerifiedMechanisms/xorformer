# Linear threshold functions

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. The function $f$ is a **linear threshold function** if there exist $\beta_0\in\mathbb{R}$ and $\beta\in\mathbb{R}^n$ such that the affine [score](02_score.md) $\ell$ given by

$$ \ell(x)=\beta_0+\beta^\top x $$

[classifies](03_classification.md) $f$. Thus $f(x)=1$ exactly when $\ell(x)\gt0$.

The coefficient vector $\beta$ may vanish, so constant functions are included. The score $\ell(x)$ may equal zero on false inputs.
