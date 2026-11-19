# Head complexity

For $n\in\mathbb{Z}_{\geq1}$ and a Boolean function $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$, its **head complexity** $H^{\ast}(f)$ is defined by

$$ H^{\ast}(f)=\min\lbrace H\in\mathbb{Z}_{\geq0}:f\text{ is computable with }H\text{ heads}\rbrace, $$

using [computability](04_computability.md) as defined above. The minimum of an empty feasible set is $\infty$. Zero heads are permitted; only the head count is minimized.
