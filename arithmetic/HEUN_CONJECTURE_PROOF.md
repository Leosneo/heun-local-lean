# Mori–Takemura Conjecture 1: finite jets determine the connection root

27 September 2026. Candidate proof, independently derived by the arithmetic agent. The argument is complete under the nonresonance and distinct-eigenvalue assumptions in the source. Priority requires a separate literature audit.

## Published target and hypotheses

Mizuki Mori and Kouichi Takemura, *On zeros of polynomials associated with Heun class equations*, [arXiv:2503.10355v3](https://arxiv.org/html/2503.10355v3), 24 October 2025, Conjecture 1, equation (4.30).

The source considers Heun, singly confluent Heun, and reduced singly confluent Heun equations. Its Section 4 assumes that D_m=m(m−1+γ+δ) are pairwise distinct, equivalently γ+δ is not a nonpositive integer. The endpoint connection construction uses γ,δ not integers. The conjecture identifies the Taylor coefficients of the connection-coefficient zero near −D_k with stabilized coefficients of finite polynomial roots. The source already proves finite-root stabilization in Proposition 4.7; that result must be credited, not presented as new.

## Common notation

For each of the three equations, the solution normalized at z=0 is

    y(z;B,s) = Σ_{l≥0} c_l(B,s) z^l,    c_0=1, c_{−1}=0,

with recurrence

    (m+1)(m+γ)c_{m+1}
      = (B+D_m+sE_m)c_m − sF_m c_{m−1}.

The coefficient pairs are

| Family | E_m | F_m |
|---|---|---|
| Heun | m(m−1+γ+ε) | (m−1+α)(m−1+β) |
| Singly confluent | m | m−1+α |
| Reduced singly confluent | 0 | 1 |

Heun additionally has γ+δ+ε=α+β+1. At z=1, choose the normalized Frobenius basis u(z;B,s), v(z;B,s), where u is holomorphic and v=(1−z)^(1−δ) times a holomorphic unit. Along a fixed connection path,

    y = d_1(B,s)u + d_2(B,s)v.

For fixed k, the desired branch is B_k(0)=−D_k and d_2(B_k(s),s)=0.

## Lemma 1: analytic connection data

Near (B,s)=(−D_k,0), normalized local Frobenius solutions at 0 and 1 depend holomorphically on both parameters. This follows either from their convergent recurrences with nonzero nonresonant denominators, or the usual analytic dependence theorem for regular singular equations. Use fixed small endpoint disks and an intervening compact path free of singularities. For Heun take |s| small enough that 1/s stays outside this path and these disks; for both confluent families no moving finite singularity occurs. Continue the local solutions by an ordinary analytic first-order system along this path.

Their connection coefficients are holomorphic: at a fixed interior point they are obtained by inversion of the nonsingular two-by-two fundamental matrix formed by u,v and their derivatives. This establishes local analyticity without exchanging any infinite-index limit with differentiation.

## Lemma 2: the hypergeometric connection zero is simple

At s=0 all three equations reduce to

    z(z−1)y'' + [(γ+δ)z−γ]y' + By = 0.

Put ρ=γ+δ−1 and choose a+b=ρ, ab=B. The Gauss connection formula gives

    d_2(B,0) = Γ(γ) Γ(δ−1) / [Γ(a) Γ(b)].

At B=−D_k one can choose a=−k, b=k+ρ. Except when k=0,ρ=0, the two roots a,b are distinct and b is not a nonpositive integer under the assumptions. Thus 1/Γ(a) has a simple zero, 1/Γ(b) is nonzero, and da/dB=1/(b−a) is nonzero. Hence ∂_B d_2(−D_k,0)≠0.

The exceptional allowed case k=0,ρ=0 needs no exclusion. Use

    1/[Γ(a)Γ(b)] = B/[Γ(1+a)Γ(1+b)].

The denominator is a symmetric holomorphic function of a,b and equals 1 at a=b=0. Consequently the zero at B=0 is again simple. The nonzero prefactor Γ(γ)Γ(δ−1) is finite because γ,δ are nonintegers.

The analytic implicit function theorem therefore supplies a unique convergent holomorphic branch B_k(s) near zero.

## Lemma 3: finite-root jets give polynomial solution jets

Write the source's analytic root of c_l(B,s) near −D_k as

    B_{k,l}(s)=−D_k−Σ_{r≥1} D_k^[r],(l) s^r,    l≥k+1.

Proposition 4.7 proves that the r-th coefficient is independent of l once l≥k+r+1. Denote that stabilized coefficient by A_r=D_k^[r],(k+r+1).

Fix J≥0 and set

    P_J(s)=−D_k−Σ_{r=1}^J A_r s^r.

For every l≥k+J+1, the Taylor jets of P_J and B_{k,l} agree through order J. Since c_l(B_{k,l}(s),s)=0 and c_l is holomorphic,

    c_l(P_J(s),s)=O(s^(J+1)).

This is an individual exact Taylor-jet statement for every l; it requires no uniform estimate as l grows. The jointly analytic germ y(z;P_J(s),s) at z=s=0 consequently has an expansion

    y(z;P_J(s),s)=Σ_{r=0}^J p_r(z)s^r + O(s^(J+1)),

where each p_r is a polynomial of degree at most k+J. In fact applying the same reasoning at order r gives the sharper bound deg p_r≤k+r. Differentiation in s commutes with extraction of Taylor coefficients in z on a small bidisk by holomorphy.

Each p_r remains this same polynomial after continuation along the connection path: analytic continuation is unique, and the continued solution is holomorphic in s. Thus the solution jets are regular at z=1.

## Lemma 4: regular polynomial jets force the singular connection jet to vanish

Substitute B=P_J(s) in y=d_1u+d_2v. All factors are holomorphic in s near zero, with u holomorphic at z=1 and v=(1−z)^(1−δ) times a holomorphic unit there. The exponent does not depend on s.

Suppose r≤J is the least index with a nonzero coefficient in d_2(P_J(s),s). In the s^r coefficient of the connection identity, the singular contribution is precisely that nonzero scalar times v(z;−D_k,0). Contributions from lower d_2 coefficients vanish; the d_1u contribution is holomorphic at 1. But the left side is the polynomial p_r. This is impossible because δ is not an integer, so a nonzero multiple of v is not holomorphic at 1. Therefore

    d_2(P_J(s),s)=O(s^(J+1)).

## Conclusion

Because the connection zero is simple, locally

    d_2(B,s)=(B−B_k(s)) g(B,s),    g(−D_k,0)≠0.

Lemma 4 implies P_J(s)−B_k(s)=O(s^(J+1)). This holds for every J. Thus the convergent Taylor expansion of the actual connection root is

    B_k(s)=−D_k−Σ_{j≥1} D_k^[j],(k+j+1) s^j,

for every k≥0 and all three families, proving the stated local perturbative conjecture under its existing hypotheses. The radius may depend on k and the fixed equation parameters. No global convergence for arbitrary s, no uniform radius in k, and no resonant extension is asserted.

## Independent algebraic explanation

Write each equation as (L_0+sV+B)y=0, where

    L_0=z(z−1)∂²+[(γ+δ)z−γ]∂.

This operator preserves polynomial degree and has distinct eigenvalues D_m on the polynomial filtration. The perturbation V raises degree by at most one:

    Heun: V=−z²(z−1)∂²−[γz(z−1)+δz²+εz(z−1)]∂−αβz;
    confluent: V=−z(z−1)∂−αz;
    reduced: V=−z.

Starting at the degree-k polynomial eigenfunction, order j can reach only degree k+j. Projection onto the degree-k eigenspace selects the eigenvalue correction; inversion on all other polynomial eigenspaces selects the eigenfunction correction, followed by normalization at zero. This independently explains the finite-jet bound and why all three equation families obey the same mechanism.

## Gcoy provenance and limits

GcoySolver.txt, approximately lines 109338–110743, proposes operator grammar, jet/companion representations, finite probes, and connection or monodromy data as the target instead of an elementary function formula. The proof above implements that viewpoint: finite coefficient probes determine each perturbation jet; endpoint regularity turns those jets into global connection information. The classical Weyl-module, Frobenius, hypergeometric, and implicit-function ingredients are not claimed as Gcoy inventions.

Several corpus statements must not be used: imposing A²=X and [A,X]=I simultaneously as operator identities is inconsistent; the correct Airy condition is (D²−X)v=0 on a vector in a Weyl module. Also [S−I,N]=S, not I. Residue exponentials determine local conjugacy data, not all common-basepoint monodromy matrices without connection information. None of these invalid claims enters this proof.
