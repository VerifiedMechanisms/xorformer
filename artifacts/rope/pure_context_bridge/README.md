# Exact auxiliary contexts for pure atoms

## Centered scalar construction

Fix centered Boolean coordinates $z_i\in\lbrace-1,1\rbrace$. Suppose $s_i\gt|b_i|$ and $d\gt\sum_i s_i$. For arbitrary $n,k,\ell$, the fraction

$$ \frac{n+\sum_i(ks_i+\ell b_i)z_i}{d+\sum_i b_i z_i} $$

is an exact pure scalar atom. Choose token attention weights $a_i=s_i-b_i$ and $\widehat b_i=s_i+b_i$, query weight $\gamma=d-\sum_i s_i$, token values $v_0=\ell-k,v_1=\ell+k$, and query numerator

$$ \eta=n-\sum_i(\ell s_i+kb_i). $$

All attention weights and the query weight are strictly positive. This construction and its exact evaluation are kernel-checked as `HeadComplexity.PureRoPECenteredConstruction.atom` and `atom_eval` in `formalization/HeadComplexity/Atoms/PureRoPECenteredConstruction.lean`. It keeps token-only values and uses no positional value term. The rotation-level realization is the existing finite-position bridge in Theorem 14.

## One-hot context criterion

Fix the main-coordinate slopes $b_i,u_i$ of one head, numbers $k\neq0,\ell$, and masses

$$ s_i=\frac{u_i-\ell b_i}{k}\gt|b_i|,\qquad S=\sum_i s_i. $$

Suppose there are $A\geq1$ desired contexts with denominator and numerator intercepts $d_a,n_a$. These are the intercepts before any main-coordinate background is fixed. Put

$$ p_a=\frac{n_a-\ell d_a}{k},\qquad l_a=p_a-d_a,\qquad r_a=p_a+d_a. $$

Use $A$ auxiliary Boolean coordinates, with context $a$ setting coordinate $a$ to $1$ and all other auxiliary coordinates to $-1$. Such a one-hot construction with the specified main slopes, token values, and intercept pairs exists if and only if

$$ \min_a r_a+(A-1)\min_a l_a-\sum_a l_a\gt2S. $$

**Construction.** Choose $l_0\lt\min_a l_a$ and $r_0\lt\min_a r_a$ sufficiently close to those minima that the strict inequality remains true with $l_0,r_0$. Set

$$ d_0=(r_0-l_0)/2,\qquad p_0=(r_0+l_0)/2,\qquad q_a=(d_a-d_0)/2,\qquad t_a=(p_a-p_0)/2. $$

Then $t_a\gt|q_a|$. Use auxiliary denominator coefficients $q_a$, masses $t_a$, and numerator coefficients $kt_a+\ell q_a$. The complete centered denominator intercept is $d_0+\sum_a q_a$. Its query mass is

$$ \gamma=d_0+\sum_a q_a-S-\sum_a t_a=\frac{r_0+(A-1)l_0-\sum_a l_a}{2}-S\gt0. $$

Choose the complete numerator intercept to be

$$ k\left(p_0+\sum_a t_a\right)+\ell\left(d_0+\sum_a q_a\right). $$

At one-hot context $a$, the complete intercepts reduce exactly to $d_a,n_a$. The resulting atom is admissible on the *entire* main and auxiliary Boolean cube, including auxiliary settings not used as contexts.

The identities and inequalities are kernel-checked as `control_mass`, `query_mass`, `oneHot_denominator`, and `oneHot_numerator`. The theorem `exists_oneHot_controls` also proves existence from any lower bounds on $l_a,r_a$ satisfying the strict criterion. Finite minima give the displayed sharp criterion. Conversely, every one-hot construction has these forms for some $l_0,r_0$; positivity gives $l_0\lt\min l_a,r_0\lt\min r_a$ and the positive query-mass inequality, which implies the criterion.

## Several heads and fixed backgrounds

The same auxiliary contexts can be used for every head, while choosing each head's coefficients independently. Thus the criterion can be checked head by head. It is a criterion for this one-hot encoding; another auxiliary encoding could be more economical.

When a local parity-face fit returns intercepts after fixing a set $F_a$ of main variables to a background, subtract those background contributions first:

$$ d_a=d_{\mathrm{face},a}-\sum_{i\in F_a}b_i z_i,\qquad n_a=n_{\mathrm{face},a}-\sum_{i\in F_a}u_i z_i. $$

The mass $S$ still sums all main coordinates. Merely fitting independently positive denominators on individual faces does not establish this global pure-atom bridge.
