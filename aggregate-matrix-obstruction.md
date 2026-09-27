# Every full two-coordinate candidate has reducible digit aggregates

This strengthens [irreducible-matrix-obstruction.md](irreducible-matrix-obstruction.md) to mixed supports. It concerns the forward, full mixed-base rewriting system, with nonnegative **real** matrices and every first diagonal entry at least one. It does not assume integrality, strictness, or any condition on affine offsets.

Write \(A,B,E,F,G\) for the five digit matrices and \(C,D\) for the boundary matrices, all of size \(2\times2\). The first coordinate is indexed by zero in this note. The six weak swap inequalities are
\[
AE\ge EA,\quad AF\ge EB,\quad AG\ge FA,\quad
BE\ge FB,\quad BF\ge GA,\quad BG\ge GB. \tag{1}
\]
Four further necessary inequalities are
\[
BD\ge GD,\qquad CE\ge CB,\qquad
CF\ge CA^2,\qquad CG\ge CAB. \tag{2}
\]
The remaining full-system inequality is not needed.

**Theorem.** If (1) and (2) hold, then both
\[
P=A+B,\qquad Q=E+F+G
\]
are reducible. Thus neither aggregate can have both off-diagonal entries positive. Individual digit matrices may be singular, scalar, or reducible; all such cases are included.

This is an obstruction to a family of matrix interpretations, not a proof of the Collatz conjecture. The case where both aggregates are reducible remains outside this theorem.

## 1. Exact swaps and two elementary observations

Suppose, for a contradiction, that at least one of \(P,Q\) is irreducible. Summing (1) gives \(PQ-QP\ge0\). If \(P\) is irreducible, its positive left and right Perron vectors \(w,v\) give
\[
w^{\mathsf T}(PQ-QP)v=0.
\]
Every entry of the nonnegative commutator therefore vanishes. The argument using \(Q\) is identical when \(Q\) is irreducible. Each of the six nonnegative differences in (1) must consequently vanish:
\[
AE=EA,\quad AF=EB,\quad AG=FA,\quad
BE=FB,\quad BF=GA,\quad BG=GB. \tag{3}
\]

We repeatedly use two observations.

* If all five digits share a nonnegative right eigenvector \(u\) with \(u_0>0\), then \(u\) is strictly positive. Otherwise \(u\) is on the first coordinate axis, so every digit has zero lower-left entry and both aggregates are reducible. The same statement holds for a common nonnegative left eigenvector with positive first coordinate.
* If all five digits share positive left and right eigenvectors, with eigenvalues \(\alpha\) for \(A,B\) and \(\beta\) for \(E,F,G\), then (2) gives
  \[
  \alpha\ge\beta\ge\alpha^2. \tag{4}
  \]
  For the first inequality, project \(BD\ge GD\) by the common positive left vector; its product with \(D\) has positive first entry. For the second, apply \(CF\ge CA^2\) to the common positive right vector; its product with \(C\) has positive first entry. Hence \(\alpha=\beta=1\), since \(\alpha\ge A_{00}\ge1\).

All matrix entries and matrix products here are nonnegative. A product of matrices whose first diagonal entries are at least one has positive first diagonal entry. In particular, none of the products used below is zero.

## 2. All five digit matrices nonsingular

The exact relations give
\[
F=AGA^{-1}=BEB^{-1},
\qquad AB=EB^2E^{-1},\qquad BA=GA^2G^{-1}.
\]
Thus \(E,F,G\) have the same characteristic polynomial. Taking determinants in \(AF=EB\) gives \(\det A=\det B\), and the displayed identities give
\[
\operatorname{tr}(AB)=\operatorname{tr}(A^2)=\operatorname{tr}(B^2).
\]
The positive traces of \(A,B\) therefore agree, so \(A,B\) have the same characteristic polynomial as well.

### 2.1 Equal binary matrices

If \(A=B\), then (3) and invertibility imply \(E=F=G\) and \(AE=EA\). At least one of \(A,E\) is irreducible, because the aggregates are \(2A,3E\). A nonnegative matrix commuting with an irreducible nonnegative matrix preserves its positive left and right Perron lines. Thus all digits share positive left and right Perron vectors. Equation (4) forces both eigenvalues to be one. But whichever of \(A,E\) is irreducible has Perron eigenvalue strictly greater than its first diagonal entry, which is at least one. This is a contradiction.

### 2.2 Unequal binary matrices have a common invariant line

Suppose \(A\ne B\), and put \(N=B-A\). The trace identities imply
\[
\operatorname{tr}N=\operatorname{tr}(N^2)=\operatorname{tr}(AN)=0.
\]
Hence \(N\) is nonzero nilpotent of rank one. Write \(N=uv^{\mathsf T}\) with \(v^{\mathsf T}u=0\). Since
\[
v^{\mathsf T}Au=\operatorname{tr}(AN)=0,
\]
the line
\[
L=\operatorname{im}N=\ker N
\]
is invariant under both \(A,B\). They act on it by the same eigenvalue.

Neither \(A\) nor \(B\) can be scalar. For example, if \(A=aI\), then \(AG=FA\) gives \(G=F\); \(BG=GB\) and \(BE=FB\) then give \(E=F\); finally \(AF=EB\) and invertibility of \(E\) give \(B=aI\), contrary to \(A\ne B\). The argument for scalar \(B\) is symmetric.

For a nonscalar two-dimensional matrix, every eigenspace is one-dimensional. Therefore \(E\), commuting with \(A\), preserves \(L\); likewise \(G\) preserves \(L\), and \(F=AGA^{-1}\) preserves it. This also covers a repeated eigenvalue with a nontrivial Jordan block.

The line cannot be a coordinate axis, since then both aggregates would be triangular in the original coordinates and reducible. There are two remaining cases: \(L\) has a positive right vector, or its annihilator has a positive left vector.

### 2.3 The common positive right line is impossible

Choose a basis whose first vector is the common positive right vector. Write
\[
A=\begin{pmatrix}\alpha&x\\0&\kappa\end{pmatrix},\qquad
B=\begin{pmatrix}\alpha&x+d\\0&\kappa\end{pmatrix},\quad d\ne0,
\]
and
\[
E=\begin{pmatrix}\beta&y\\0&\tau\end{pmatrix},\quad
F=\begin{pmatrix}\beta&y+e\\0&\tau\end{pmatrix},\quad
G=\begin{pmatrix}\beta&y+g\\0&\tau\end{pmatrix}.
\]
The common positive eigenvector makes \(\alpha,\beta\) their respective Perron eigenvalues. In particular \(\alpha>0\) and \(|\kappa|\le\alpha\). The common ternary diagonal entries follow from the two similarity formulas, whose conjugating matrices preserve \(L\).

Subtracting the baseline \(AE=EA\) equation from the other equations in (3) gives
\[
\alpha e=\beta d,\qquad
(\tau-\beta)d=\kappa e,\qquad
\alpha g=\kappa e,\qquad
(\alpha-\kappa)g=(\beta-\tau)d.
\]
Eliminating \(e,g,\tau\) gives \(\kappa(2\alpha-\kappa)=0\). Nonsingularity excludes \(\kappa=0\), and \(|\kappa|\le\alpha\) excludes \(\kappa=2\alpha\).

### 2.4 The common positive left line is also impossible

In this case use the transposed triangular shape:
\[
A=\begin{pmatrix}\alpha&0\\x&\kappa\end{pmatrix},\qquad
B=\begin{pmatrix}\alpha&0\\x+d&\kappa\end{pmatrix},\quad d\ne0,
\]
with ternary lower-left entries \(y,y+e,y+g\) and diagonals \(\beta,\tau\). The positive common left vector makes \(\alpha,\beta\) the Perron eigenvalues. The corresponding equations are
\[
\kappa e=\tau d,\qquad
(\beta-\tau)d=\alpha e,\qquad
\kappa g=\alpha e,\qquad
(\alpha-\kappa)g=(\beta-\tau)d.
\]
Since \(\kappa,\tau,d\ne0\), we have \(g\ne0\), and the last two equations force \(\alpha=2\kappa\). Substitution gives \(\beta=3\tau\). Set \(\mu=\kappa>0,\nu=\tau>0\). The baseline equation gives
\[
E=\frac{2\nu}{\mu}A-\nu I,\quad
F=\frac{\nu}{\mu}(A+B)-\nu I,\quad
G=\frac{2\nu}{\mu}B-\nu I. \tag{5}
\]

Let \(w^{\mathsf T}>0\) be the common left vector. The Perron eigenvalues are simple. Choose nonnegative right Perron vectors \(v_a,v_b\) normalized by \(w^{\mathsf T}v_a=w^{\mathsf T}v_b=1\). These vectors need not individually be positive. Their spectral projectors give
\[
\begin{aligned}
A&=\mu I+\mu v_aw^{\mathsf T},&
B&=\mu I+\mu v_bw^{\mathsf T},\\
E&=\nu I+2\nu v_aw^{\mathsf T},&
G&=\nu I+2\nu v_bw^{\mathsf T}.
\end{aligned} \tag{6}
\]
In particular, with \(s=v_a+v_b\),
\[
P=2\mu I+\mu s w^{\mathsf T},\qquad
Q=3\nu I+3\nu s w^{\mathsf T}.
\]
Aggregate irreducibility is equivalent here to \(s>0\).

Projecting \(BD\ge GD\) by \(w^{\mathsf T}\) gives \(2\mu\ge3\nu\). Put
\[
u=(Cv_a)_0\ge0,\qquad v=(Cv_b)_0\ge0.
\]
Since \(s>0\) and \(C_{00}\ge1\), we have \(u+v>0\). Evaluate \(CE\ge CB\) on \(v_a\) and \(CG\ge CAB\) on \(v_b\). They give
\[
3\nu u\ge\mu(u+v),\qquad
3\nu v\ge2\mu^2(u+v).
\]
Together with \(2\mu\ge3\nu\), these imply \(u\ge v>0\) and
\[
\mu\le\frac{v}{u+v}\le\frac12.
\]
But \(w^{\mathsf T}v_a=1\) and nonnegativity give
\[
1\le A_{00}=\mu(1+(v_a)_0w_0)\le2\mu\le1.
\]
Equality throughout forces \(\mu=1/2\) and \((v_a)_1=0\). The same argument for \(B\) gives \((v_b)_1=0\), contradicting \(s>0\).

This completes the nonsingular case without assuming any individual digit is irreducible.

## 3. A binary digit matrix is singular

Any singular nonnegative \(2\times2\) matrix with positive first diagonal entry is rank one and can be written \(ua^{\mathsf T}\), with \(u,a\ge0\) and \(u_0,a_0>0\). Its nonzero eigenvalue is \(a^{\mathsf T}u>0\).

### 3.1 Exactly one binary matrix is singular

Suppose \(A=ua^{\mathsf T}\) is singular and \(B\) is nonsingular. The relation \(AF=EB\) forces \(E\) to have rank one. Since \(A,E\) commute and their product is nonzero, their rank-one images and row spaces coincide; thus \(E=tA\) for some \(t>0\). Put
\[
\alpha=a^{\mathsf T}u,\qquad\beta=t\alpha.
\]
The relation \(BE=FB\) gives \(F=BEB^{-1}\), so \(F\) is rank one with nonzero eigenvalue \(\beta\).

From \(AG=FA\), the nonzero rank-one images give \(Fu=\zeta u\) for some \(\zeta>0\). Since \(F\) has only one nonzero eigenvalue, \(\zeta=\beta\), and its image is \(\mathbb Ru\). But the similarity formula also gives image \(F=\mathbb RBu\), so \(Bu=bu\) for some \(b>0\). From \(BF=GA\), we obtain \(Gu=gu\) for some \(g>0\). Evaluating \(AG=FA\) and \(AF=EB\) on \(u\) then gives \(g=\beta\) and \(b=\alpha\).

All five digits therefore share the nonnegative right vector \(u\), so aggregate irreducibility forces \(u>0\). Moreover,
\[
BF=\alpha F,\qquad GA=\beta A,
\]
so \(BF=GA\) yields \(F=(\beta/\alpha)A=E\). The equations \(AF=EB\) and \(AG=FA\) now give
\[
a^{\mathsf T}B=\alpha a^{\mathsf T},\qquad
a^{\mathsf T}G=\beta a^{\mathsf T}.
\]
Thus \(a^{\mathsf T}\) is common to all five digits and aggregate irreducibility forces \(a>0\). We have common positive left and right vectors with binary eigenvalue \(\alpha\) and ternary eigenvalue \(\beta\). Equation (4) forces \(\alpha=1\), whereas the positive rank-one matrix \(A\) satisfies \(\alpha>A_{00}\ge1\), a contradiction.

The case where \(B\) is singular and \(A\) nonsingular follows by the symmetry \(A\leftrightarrow B, E\leftrightarrow G\) of (3). This symmetry is used only to obtain common vectors and common binary/ternary eigenvalues; the same original boundary inequalities (2) then give the contradiction.

### 3.2 Both binary matrices are singular: dependent right factors

Write \(A=ua^{\mathsf T}\), \(B=vb^{\mathsf T}\), with the first coordinates of all four nonnegative vectors positive. If \(u,v\) are proportional, rescale to write \(B=ub^{\mathsf T}\).

The equations \(AE=EA\), \(AG=FA\), and \(BG=GB\) show that \(u\) is a common right eigenvector of \(E,F,G\), with positive eigenvalues. Their equality follows by evaluating \(AG=FA\) and \(BE=FB\) on \(u\); denote the common value by \(\beta\). Aggregate irreducibility forces \(u>0\), so \(\beta\) is the Perron eigenvalue of \(F\).

The other two relations give
\[
a^{\mathsf T}F=\beta b^{\mathsf T},\qquad
b^{\mathsf T}F=\beta a^{\mathsf T}.
\]
Consequently \(a^{\mathsf T}-b^{\mathsf T}\), if nonzero, would be a left eigenvector of \(F\) with eigenvalue \(-\beta\). A nonnegative two-dimensional matrix with Perron eigenvalue \(\beta\) and positive trace cannot have eigenvalue \(-\beta\). Here \(\operatorname{tr}F\ge F_{00}\ge1\). Thus \(a=b\) and \(A=B\).

The displayed equations and (3) make \(a^{\mathsf T}\) a common left eigenvector, which aggregate irreducibility forces positive. We again obtain (4) and the contradiction \(\rho(A)>A_{00}\ge1\).

### 3.3 Both binary matrices are singular: independent right factors

Now suppose \(u,v\) are linearly independent. Commutation \(AE=EA\) shows \(Eu\in\mathbb Ru\), and \(AF=EB\) shows \(Ev\in\mathbb Ru\). Both images are nonzero. Thus \(E\) has rank one, and commutation with \(A\) gives \(E=tA\), \(t>0\). Similarly, \(BG=GB\) and \(BF=GA\) give \(G=sB\), \(s>0\).

The equation \(AG=FA\) now reads
\[
s\,u(a^{\mathsf T}v)b^{\mathsf T}=(Fu)a^{\mathsf T}.
\]
The coefficient \(a^{\mathsf T}v\) is positive, so \(b\) is proportional to \(a\). Rescale \(v\) to write \(B=va^{\mathsf T}\). The relation \(AF=EB\) then also shows that \(a^{\mathsf T}\) is a left eigenvector of \(F\). All five digits share this nonnegative left vector, which aggregate irreducibility forces positive.

Put \(\alpha=a^{\mathsf T}u\), \(\gamma=a^{\mathsf T}v\). The equations \(AG=FA\), \(BE=FB\) give
\[
Fu=s\gamma u,\qquad Fv=t\alpha v.
\]
Since the common left vector has nonzero pairing with both \(u,v\), these two eigenvalues are equal; call the common value \(\beta\). Independence of \(u,v\) then gives \(F=\beta I\). The equation \(AF=EB\) gives \(\beta=t\gamma\), while \(\beta=t\alpha\); hence \(\gamma=\alpha\).

Thus the common left vector has eigenvalue \(\alpha\) for \(A,B\), and \(\beta\) for \(E,F,G\). Projecting \(BD\ge GD\) gives \(\alpha\ge\beta\). Applying \(CF\ge CA^2\) to \(u\) gives \(\beta\ge\alpha^2\), because \((Cu)_0>0\). Therefore \(\alpha=\beta=1\).

But
\[
1\le A_{00}=u_0a_0\le a^{\mathsf T}u=1
\]
and \(a_1>0\) force \(u_1=0\). The same argument for \(B\) forces \(v_1=0\), contradicting independence.

This exhausts all cases with a singular binary digit.

## 4. Binary digits nonsingular, a ternary digit singular

The similarity relations \(F=AGA^{-1}=BEB^{-1}\) make \(E,F,G\) all rank one, with the same positive nonzero eigenvalue \(\beta\). Write \(E=ue^{\mathsf T}\) with \(u,e\ge0\), \(u_0,e_0>0\). From \(AE=EA\), we have \(Au=\alpha_Au\), with \(\alpha_A>0\). Hence
\[
F=A^{-1}EB
\]
has image \(\mathbb Ru\). But \(F=BEB^{-1}\) has image \(\mathbb RBu\), so \(Bu\) is proportional to \(u\). The relation \(G=A^{-1}FA\) gives the same image for \(G\). All five digits share the nonnegative right vector \(u\), which aggregate irreducibility forces positive.

Normalize the factorizations as
\[
E=ue^{\mathsf T},\quad F=uf^{\mathsf T},\quad G=ug^{\mathsf T},
\qquad e^{\mathsf T}u=f^{\mathsf T}u=g^{\mathsf T}u=\beta.
\]
Evaluating \(AF=EB\) on \(u\) makes the binary right eigenvalues equal; call the common Perron value \(\alpha\). The equations \(AG=FA\), \(BF=GA\) give
\[
f^{\mathsf T}A=\alpha g^{\mathsf T},\qquad
g^{\mathsf T}A=\alpha f^{\mathsf T}.
\]
As in section 3.2, positive trace excludes eigenvalue \(-\alpha\), so \(f=g\). The equations \(AF=EB\), \(BE=FB\) similarly force \(e=f\). Thus the common left vector \(e\) is also positive by aggregate irreducibility.

Equation (4) gives \(\alpha=\beta=1\). But \(E=ue^{\mathsf T}\) is positive, so \(\beta>E_{00}\ge1\), the final contradiction.

All possible singularity patterns have now been covered. Therefore both digit aggregates must be reducible.

## 5. The five digits share an original-coordinate triangular orientation

Write the upper-right and lower-left entries of \(P\) as \(q_P,r_P\), and similarly use \(q_Q,r_Q\) for \(Q\). The sum of the original weak swap inequalities still gives \(PQ-QP\ge0\), whether or not either aggregate is irreducible. Its two diagonal entries are
\[
q_Pr_Q-q_Qr_P,\qquad q_Qr_P-q_Pr_Q.
\]
Both must be nonnegative, so
\[
q_Pr_Q=q_Qr_P. \tag{7}
\]
The theorem gives \(q_Pr_P=q_Qr_Q=0\). If one aggregate is strictly upper triangular off the diagonal and the other strictly lower triangular off the diagonal, (7) fails. Thus both are upper triangular, or both are lower triangular; a diagonal aggregate is compatible with either orientation.

Every summand is nonnegative. A zero off-diagonal entry in an aggregate is therefore zero in every digit contributing to it. Consequently all five digit matrices are upper triangular in the original coordinates, or all five are lower triangular in the original coordinates. No change of basis is required for this conclusion. It makes no assertion about the boundary matrices \(C,D\).

## 6. Reversed words have the same necessary matrix obstruction

Here reversal means reversing the order of symbols on both sides of each rule, while preserving the direction of the rule. Suppose matrices \(M_\sigma\) satisfy the weak matrix inequalities for these reversed words, with the same nonnegativity and first-diagonal conditions. Set
\[
N_\sigma=M_\sigma^{\mathsf T}
\]
for each of the seven symbols. For every word \(w\),
\[
\bigl(M_{\operatorname{rev}(w)}\bigr)^{\mathsf T}=N_w.
\]
Transposing each reversed-word inequality therefore gives exactly the corresponding forward-word inequality for the \(N\) matrices. Transposition preserves nonnegativity and first diagonal entries, so the theorem applies. It also preserves reducibility. Hence both digit aggregates of the \(M\) matrices are reducible, and section 5 applied to \(N\) shows that all five original digit matrices share a triangular orientation as well.

This is a correspondence of necessary **matrix inequalities**. No correspondence between affine offsets is asserted or needed. It therefore gives the same obstruction to forward and reversed full affine interpretations under the stated matrix conditions.

## Scope of the result

The theorem and its transpose corollary cover forward and reversed full-system matrix inequalities with the explicit condition \(M_{00}\ge1\) for every symbol. They do not establish the same conclusion for top rewriting, matrices with unrestricted first diagonal entries, or higher dimensions. They also do not exclude all interpretations with triangular digit matrices.

No finite coefficient bound, trajectory search, or numerical solver result is used.
