# Real affine interpretations with a uniform strict gap

Nonnegative real coefficients can give sound relative-termination certificates. Integrality is not required when every strict rule has a uniform first-coordinate gap of at least one. The current search obtained no such model.

Let the carrier be \(D=\mathbb R_{\ge0}^d\). Define

\[
x\succeq y\iff x_i\ge y_i\text{ for every }i,
\qquad
x\succ_1 y\iff x\succeq y\text{ and }x_1-y_1\ge1.
\]

The strict relation is well-founded: a chain starting at \(x\) has at most \(\lfloor x_1\rfloor\) strict steps, since its first coordinate stays nonnegative and decreases by at least one each time. Weak steps can be interspersed without increasing that bound.

Interpret each symbol by \(F_\sigma(x)=M_\sigma x+v_\sigma\), with real nonnegative coefficients and \((M_\sigma)_{11}\ge1\). Each map preserves the carrier and the weak order. If \(x\succ_1y\), then

\[
\bigl(F_\sigma(x)-F_\sigma(y)\bigr)_1
=\sum_j(M_\sigma)_{1j}(x_j-y_j)
\ge(M_\sigma)_{11}(x_1-y_1)\ge1.
\]

All other coordinate differences remain nonnegative. Thus every symbol, and hence every prefix context, preserves \(\succ_1\).

Suppose every rule \(\ell\to r\) satisfies the entrywise inequalities

\[
M_\ell\ge M_r,\qquad v_\ell\ge v_r.
\]

For any \(x\in D\), these imply \(F_\ell(x)\succeq F_r(x)\). If a selected rule also satisfies

\[
(v_\ell)_1-(v_r)_1\ge1,
\]

then \(F_\ell(x)\succ_1F_r(x)\) uniformly for every \(x\in D\). A suffix supplies another point of \(D\); a prefix preserves the comparison. Therefore this weak or strict decrease holds for rewriting in arbitrary contexts.

Evaluating complete words at \(0\in D\) now proves that selected strict rules occur only finitely often in any derivation. They may be removed in the usual relative-termination argument. Full termination still requires termination of the residual system, possibly through further independently verified stages.

This is a sufficient theorem for the exact real constraints emitted by `unbounded-matrix-search.py`. A floating-point approximation or an unverified solver status does not establish the inequalities. Rational candidates can be checked using exact fractions; algebraic candidates require exact algebraic arithmetic or certified sign comparisons. The existing integer-only checker deliberately rejects noninteger coefficients and cannot validate this larger certificate class.
