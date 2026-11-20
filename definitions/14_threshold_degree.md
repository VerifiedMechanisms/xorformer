# Definition 1.14. Threshold degree

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. Its **threshold degree** $\deg _{\pm}(f)$ is the minimum total degree of a real polynomial that [strictly sign-represents (Definition 1.13)](13_strict_sign_representation.md) $f$:

$$ \deg_{\pm}(f)=\min\lbrace\deg P:P\in\mathbb{R}[x_1,\ldots,x_n]\text{ strictly sign-represents }f\rbrace. $$

The minimum of an empty feasible set is $\infty$. The zero polynomial is excluded by the strict sign condition; nonzero constant polynomials have degree zero.
