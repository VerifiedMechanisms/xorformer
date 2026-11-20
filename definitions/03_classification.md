# Definition 1.3. Classification

A [score](02_score.md) $\Phi$ **classifies** a Boolean function $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ if, for every input $x$,

$$ f(x)=1\quad\Longrightarrow\quad\Phi(x)\gt0, \qquad f(x)=0\quad\Longrightarrow\quad\Phi(x)\lt0. $$

Thus a classifying score is nonzero on every Boolean input. A score may vanish when no classification requirement is imposed.

**Threshold ties.** Requiring strict signs preserves the labelings realizable with each head count. To see this, suppose a score $\Phi$ satisfies only $f(x)=1$ exactly when $\Phi(x)\gt0$. If there is a true input, finiteness of the cube gives

$$ m=\min\lbrace\Phi(x):f(x)=1\rbrace\gt0, \qquad \varepsilon=m/2. $$

If there are no true inputs, take $\varepsilon=1$. In either case, $\Phi-\varepsilon$ is positive on every true input and negative on every false input. For a realized score, this shift replaces $\tau$ by $\tau+\varepsilon$ without changing the attention heads. Conversely, every strict classifier satisfies the rule above. This argument also covers both constant functions.
