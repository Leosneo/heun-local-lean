> Historical research draft. The compiled theorem proves local branch existence
> and convergence, not global completeness of the zero list. Stronger informal
> claims in this draft are not all certified by Lean. See README.md and the
> Lean-aligned INFORMAL_PROOF.md for the precise current scope.

# Finite polynomial jets determine Heun connection roots

Research proof, 27 September 2026.

**Lean verification update:** the local convergent-series assertion is proved
as `Heun.literatureConjecture : Heun.LiteratureConjecture` in
[`lean/HeunCompletion.lean`](lean/HeunCompletion.lean), with only standard
Lean axioms. Its checked proof uses a bounded-sequence eigenpair construction
instead of the Gamma connection formula in Section 3 below. The formal
theorem does not separately assert the stronger simple-zero or uniqueness
claims about the accessory branch made in this informal argument. See
[`lean/README.md`](lean/README.md) for the exact certified scope.

**Result.** The argument below proves the local convergent-series assertion of Mori–Takemura's Conjecture 1 for Heun, singly confluent Heun, and reduced singly confluent Heun equations, under the source's nonresonance and distinctness assumptions. It supplies the connection-root step beyond the finite-root stabilization already proved by those authors. Three agents and the coordinating agent checked the argument or its source scope within this session. This is a written mathematical proof, not a Lean formalization or external peer review. No earlier resolution was found in the targeted literature search; that is not a guarantee of priority.

## 1. Exact target and notation

The target is Conjecture 1, equation (4.30), in Mizuki Mori and Kouichi Takemura, *On zeros of polynomials associated with Heun class equations*, [arXiv:2503.10355v3](https://arxiv.org/html/2503.10355v3), 24 October 2025. The inspected current arXiv record retains this conjecture. No peer-reviewed publication status is assumed.

Fix complex parameters satisfying

\[
\gamma,\delta\notin\mathbb Z,
\qquad \gamma+\delta\notin\mathbb Z_{\leq0}.
\]

Put \(D_m=m(m-1+\gamma+\delta)\). The second assumption is equivalent to pairwise distinctness of \(D_0,D_1,\ldots\). Indeed

\[
D_m-D_n=(m-n)(m+n-1+\gamma+\delta).
\]

Let \(\partial=d/dz\) and

\[
L_0=z(z-1)\partial^2+[(\gamma+\delta)z-\gamma]\partial.
\]

All three equations, after clearing denominators, have the form

\[
(L_0+sV+B)y=0.
\tag{1}
\]

The operators are

\[
\begin{aligned}
V_{\rm H}&=-z^2(z-1)\partial^2
-\{z[(\gamma+\delta)z-\gamma]+\epsilon z(z-1)\}\partial
-\alpha\beta z,\\
V_{\rm C}&=-z(z-1)\partial-\alpha z,\\
V_{\rm R}&=-z.
\end{aligned}
\]

In the Heun case impose \(\gamma+\delta+\epsilon=\alpha+\beta+1\). These are the equations in the source's (3.5), (3.11), and (3.15). We work near \(s=0\), taking \(|s|<1\) in the Heun case.

Normalize the solution regular at zero by

\[
y(z;B,s)=\sum_{m\ge0}c_m(B,s)z^m,\qquad c_0=1,\quad c_{-1}=0.
\]

Its recurrence is

\[
(m+1)(m+\gamma)c_{m+1}
=(B+D_m+sE_m)c_m-sF_mc_{m-1},
\tag{2}
\]

with

| Family | \(E_m\) | \(F_m\) |
|---|---|---|
| Heun | \(m(m-1+\gamma+\epsilon)\) | \((m-1+\alpha)(m-1+\beta)\) |
| Singly confluent | \(m\) | \(m-1+\alpha\) |
| Reduced singly confluent | \(0\) | \(1\) |

Choose a fixed connection path from a neighborhood of zero to a neighborhood of one, corresponding to the ordinary interval between these endpoints. At one use the normalized Frobenius basis

\[
u(z;B,s)=1+O(1-z),\qquad
v(z;B,s)=(1-z)^{1-\delta}(1+O(1-z)),
\]

with a fixed branch. Define the connection coefficients by

\[
y=d_1(B,s)u+d_2(B,s)v.
\tag{3}
\]

Thus \(d_2=0\) means that the solution normalized at zero is also regular at one.

At \(s=0\), equation (2) gives

\[
c_N(B,0)=\frac{\prod_{m=0}^{N-1}(B+D_m)}{N!(\gamma)_N}.
\tag{4}
\]

For \(N\ge k+1\) the root \(-D_k\) is simple. Write its unique local analytic continuation as

\[
B_{k,N}(s)=-D_k-\sum_{j\ge1}D_k^{[j],(N)}s^j.
\tag{5}
\]

**Theorem.** For every fixed \(k\ge0\), there is a unique holomorphic zero branch \(B_k(s)\) of \(d_2\) near \((-D_k,0)\), and on a sufficiently small disk its convergent Taylor expansion is

\[
\boxed{B_k(s)=-D_k-\sum_{j\ge1}D_k^{[j],(k+j+1)}s^j.}
\tag{6}
\]

This is the conjectured expansion. The radius may depend on \(k\) and the fixed parameters. No uniform radius, global continuation in \(s\), resonant extension, or classification of roots escaping to infinity is claimed.

## 2. Formal solution coefficients have finite polynomial degree

On monomials,

\[
L_0z^m=D_mz^m-m(m-1+\gamma)z^{m-1}.
\]

Consequently each finite polynomial space \(\mathcal P_N\) is invariant under \(L_0\), and its triangular matrix has distinct diagonal entries \(D_0,\ldots,D_N\). There are compatible polynomial eigenvectors \(\phi_m\) of degree \(m\) with

\[
L_0\phi_m=D_m\phi_m,\qquad \phi_m(0)=1.
\]

The normalization is possible because a solution regular at zero with zero constant term must vanish identically: recurrence (2) at \(s=0\) determines all subsequent coefficients from the constant term, and its denominators are nonzero.

Crucially, every operator \(V\) above sends \(\mathcal P_N\) into \(\mathcal P_{N+1}\).

We construct formal series

\[
\lambda(s)=D_k+\sum_{j\ge1}\lambda_js^j,
\qquad p(z,s)=\sum_{j\ge0}p_j(z)s^j
\]

satisfying \((L_0+sV-\lambda(s))p=0\), with

\[
p_0=\phi_k,\qquad p_j(0)=0\ (j>0),
\qquad \deg p_j\le k+j.
\tag{7}
\]

Suppose the construction is complete through order \(j-1\). The order-\(j\) equation is

\[
(L_0-D_k)p_j
=-Vp_{j-1}+\sum_{a=1}^{j-1}\lambda_ap_{j-a}+\lambda_j\phi_k.
\tag{8}
\]

The known terms lie in \(\mathcal P_{k+j}\). Express them in the eigenbasis \(\phi_0,\ldots,\phi_{k+j}\). The vanishing of their total \(\phi_k\) coefficient uniquely determines \(\lambda_j\). For every other component, divide by \(D_m-D_k\) to obtain \(p_j\). Finally add a unique multiple of \(\phi_k\) to enforce \(p_j(0)=0\). This proves existence, uniqueness, and (7) at every order.

Nothing here assumes convergence of either formal series.

## 3. The connection coefficient is holomorphic and has a simple base zero

The regular singularities at zero and one have fixed exponent pairs \((0,1-\gamma)\) and \((0,1-\delta)\). On a small parameter neighborhood of \((-D_k,0)\), normalized Frobenius solutions depend holomorphically on \((B,s)\) on fixed endpoint disks. The noninteger exponents make the Frobenius denominators nonzero. For Heun the remaining singularity \(1/s\) stays outside a fixed neighborhood of the connecting interval after shrinking the parameter disk.

Continue the solutions to an ordinary point of that interval by their first-order linear systems. Holomorphic dependence on parameters is preserved. The matrix consisting of \(u,v\) and their derivatives has nonzero determinant there. Inverting it in (3) shows that \(d_1,d_2\) are jointly holomorphic in \((B,s)\).

At \(s=0\), let \(\rho=\gamma+\delta-1\), and choose \(a+b=\rho\), \(ab=B\). The [Gauss connection formula](https://dlmf.nist.gov/15.10.E21) gives

\[
d_2(B,0)=\frac{\Gamma(\gamma)\Gamma(\delta-1)}{\Gamma(a)\Gamma(b)}.
\tag{9}
\]

At \(B=-D_k\), take \(a=-k\), \(b=k+\rho\). For \(k\ge1\), the assumptions imply that \(b\) is not a nonpositive integer and \(2k+\rho\ne0\). The reciprocal gamma function has a simple zero at \(-k\), giving

\[
\partial_Bd_2(-D_k,0)
=\frac{\Gamma(\gamma)\Gamma(\delta-1)(-1)^k k!}
{(2k+\rho)\Gamma(k+\rho)}\ne0.
\tag{10}
\]

For \(k=0\), the uniformly valid expression is

\[
\partial_Bd_2(0,0)
=\frac{\Gamma(\gamma)\Gamma(\delta-1)}{\Gamma(\gamma+\delta)}\ne0.
\tag{11}
\]

In particular the allowed case \(\gamma+\delta=1\) is included. Although \(a=b=0\) there and the separate roots need not be analytic in \(B\), the identity

\[
\frac1{\Gamma(a)\Gamma(b)}
=\frac{B}{\Gamma(1+a)\Gamma(1+b)}=B+O(B^2)
\]

holds when \(a+b=0\). The denominator is symmetric and holomorphic, hence a holomorphic function of \(B\) near zero, with value one.

The analytic implicit function theorem now gives a unique holomorphic branch \(B_k(s)\) with \(d_2(B_k(s),s)=0\), \(B_k(0)=-D_k\).

## 4. Polynomial jets satisfy the global endpoint condition

For a fixed \(J\), put

\[
Q_J(s)=-D_k-\sum_{j=1}^J\lambda_js^j.
\]

Let \(Y(z,s)=y(z;Q_J(s),s)\) be the genuine normalized analytic solution near zero. Its \(s\)-Taylor coefficients through order \(J\) satisfy exactly equation (8) with the same normalization. Uniqueness of the inhomogeneous recurrence at zero therefore identifies them with the polynomials \(p_0,\ldots,p_J\).

Analytic continuation along the fixed path preserves these coefficient identities. On a slit neighborhood of one, expand

\[
Y(z,s)=d_1(Q_J(s),s)u(z;Q_J(s),s)
+d_2(Q_J(s),s)v(z;Q_J(s),s).
\tag{12}
\]

Suppose the first nonzero Taylor coefficient of \(d_2(Q_J(s),s)\) occurs at order \(r\le J\). At that order the right side of (12) is the sum of a function holomorphic at one and a nonzero constant times \(v(z;-D_k,0)\). All lower coefficients of \(d_2\) vanish, so no other singular term occurs. The left side is \(p_r(z)\), a polynomial. This is impossible: a nonzero multiple of \((1-z)^{1-\delta}\) times a holomorphic unit cannot extend holomorphically across one when \(\delta\notin\mathbb Z\).

Hence

\[
d_2(Q_J(s),s)=O(s^{J+1}).
\tag{13}
\]

Simplicity of the connection root gives a local factorization

\[
d_2(B,s)=(B-B_k(s))h(B,s),\qquad h(-D_k,0)\ne0.
\]

Equation (13) implies \(Q_J-B_k=O(s^{J+1})\). Since \(J\) is arbitrary, the formally constructed eigenvalue coefficients are the Taylor coefficients of the genuine analytic zero branch. This proves convergence without interchanging a large-index coefficient limit with differentiation.

## 5. Identification with the exact finite roots in the conjecture

By (7), for \(N\ge k+J+1\) every Taylor coefficient through order \(J\) of the coefficient of \(z^N\) in the normalized solution vanishes. Thus

\[
c_N(B_k(s),s)=O(s^{J+1}).
\]

The finite polynomial root in (4) is simple. Factoring \(c_N\) near that root yields

\[
B_k(s)-B_{k,N}(s)=O(s^{J+1}).
\]

Taking \(N=k+J+1\) and comparing the coefficient of \(s^J\) in (5) proves

\[
\lambda_J=D_k^{[J],(k+J+1)},
\]

which establishes (6). The same argument recovers the finite-root stabilization already proved in Proposition 4.7 of the source, but the added conclusion is its identification with the convergent global connection-root germ. \(\square\)

## 6. What Gcoy contributed, and what we learn

The relevant Gcoy ideas are to retain the differential operator as a grammar, represent its action on coefficient/jet spaces, and study a solution through its responses to specified probes. Here the operator acts on polynomial degree, and the probe is the coefficient of the singular Frobenius solution at the other endpoint.

The resulting mechanism is concrete:

\[
\text{one perturbation raises degree by at most one}
\Longrightarrow \deg p_j\le k+j
\Longrightarrow \text{every finite solution jet is endpoint-regular}
\Longrightarrow \text{the actual connection zero has those jets}.
\]

This explains why a finite recurrence can determine an exact coefficient of global spectral data: the order of perturbation limits how far the operator can propagate in the polynomial filtration. It does not mean a finite graph determines an arbitrary global solution without assumptions.

The operator-filtration viewpoint was motivated by Gcoy. Triangular linear algebra, Frobenius theory, the gamma connection formula, and the implicit function theorem are classical tools, not inventions of Gcoy. No unsupported corpus claim about universal solvability, exact neural solutions, or reconstruction of global monodromy from residue exponentials is used.

## 7. Checks and records

- `check_jets.py` independently constructs the formal eigenpair by exact rational linear algebra, verifies the differential-equation residual, and compares its coefficients to recurrence (2). All 48 cases passed through order six, including \(\gamma+\delta=1\), vanishing coupling, and signed parameters. These finite checks supplement the proof; they do not establish the analytic theorem by themselves.
- `arithmetic/HEUN_CONJECTURE_PROOF.md` gives a second route starting from the source's Proposition 4.7.
- `geometry/HEUN_ANALYTIC_JET_AUDIT.md` records the independent analytic audit.
- `reconstruction/MORI_TAKEMURA_SOURCE_AUDIT.md` records the exact source scope and bounded priority search.

Reproduce the root's finite checks with `python3 check_jets.py` from this directory. Only the Python standard library is required.
