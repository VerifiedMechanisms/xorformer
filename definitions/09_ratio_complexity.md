# Definition 1.9. Ratio complexity

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. Its **ratio complexity** $L(f)$ is the minimum $H\in\mathbb{Z} _{\geq0}$ for which there exist $H$ [admissible ratios](08_admissible_ratios.md) and a constant $c\in\mathbb{R}$ such that the score $\Phi$ given by

$$ \Phi(x)=c+\sum_{h=1}^{H}\frac{A_h^\top x+b_h}{C_h^\top x+d_h} $$

[classifies](03_classification.md) $f$. The minimum is $\infty$ if no such representation exists. For $H=0$, the sum is empty and the score is $c$.

The threshold adjustment in [Classification (Definition 1.3)](03_classification.md) changes only $c$, so requiring strict signs preserves the feasible ratio counts and their minimum.
