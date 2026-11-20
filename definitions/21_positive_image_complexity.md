# Definition 1.21. Positive-image complexity

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$.

In the minimum below, $t$ ranges over [positive weighted statistics (Definition 1.15)](15_positive_weighted_statistics.md) and $F$ over functions $\mathrm{Im}(t)\to\lbrace0,1\rbrace$. The **positive-image complexity** of $f$ is

$$ M_{+}(f)=\min\lbrace\lvert\mathrm{Im}(t)\rvert:f=F\circ t\rbrace. $$

The factorization means $f(x)=F(t(x))$ on every Boolean input. The minimum of an empty feasible set is $\infty$.
