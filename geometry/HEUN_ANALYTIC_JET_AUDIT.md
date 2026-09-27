# Independent analytic audit of Mori–Takemura Conjecture 1

Source: Mori–Takemura, *On zeros of polynomials associated with Heun class equations*, arXiv:2503.10355v3 (24 October 2025), equations (3.5), (3.11), (3.15), Proposition 4.7, Conjecture 1 / (4.30). https://arxiv.org/html/2503.10355v3

## Precise parameter regime and conclusion

Fix γ,δ not integers and γ+δ not in Z_{≤0}; in the Heun case also γ+δ+ε=α+β+1. Fix k≥0. There is a positive radius, allowed to depend on k and all fixed parameters, and a unique holomorphic zero germ B_k(s) of the connection coefficient d₂(B,s), with B_k(0)=−D_k, where D_k=k(k−1+γ+δ). Its Taylor coefficients are exactly the stabilized finite-recurrence coefficients in (4.30). This proves the conjecture as a statement about perturbative zero germs. It does not assert a common convergence radius for every k or classify roots escaping to infinity as s→0.

## Polynomial operator and normalization

Write L₀=z(z−1)∂²+[(γ+δ)z−γ]∂. In each case, after clearing denominators, the differential equation is

    (L₀+sV+B)y=0.

For Heun,

    V=−z²(z−1)∂²−{z[(γ+δ)z−γ]+εz(z−1)}∂−αβz.

For singly confluent Heun, V=−z(z−1)∂−αz; for reduced singly confluent Heun, V=−z. Each V raises polynomial degree by at most one. L₀ is triangular on monomials with diagonal D_m. The assumed pairwise distinctness of D_m gives a polynomial eigenbasis φ_m, normalized by φ_m(0)=1. The normalization is possible: the Taylor recurrence at zero with γ not a nonpositive integer implies a holomorphic homogeneous solution vanishing at zero vanishes identically.

Set λ(s)=−B(s)=D_k+Σ_{j≥1}λ_j s^j and y=Σ_{j≥0}p_j s^j, with p₀=φ_k and p_j(0)=0 for j>0. At order j,

    (L₀−D_k)p_j=−Vp_{j−1}+Σ_{a=1}^j λ_a p_{j−a}.

The right-hand side has degree at most k+j. Its φ_k component uniquely determines λ_j; invert L₀−D_k on all other φ_m components and then add a multiple of φ_k to impose p_j(0)=0. Consequently deg p_j≤k+j. This construction is formal and makes no unproved convergence assumption.

## Connection coefficient is jointly holomorphic

On a small parameter neighborhood of (B,s)=(−D_k,0), both regular singularities 0,1 retain their fixed noninteger exponent differences. Frobenius recurrences have denominators independent of B,s and nonzero; their normalized solutions are jointly holomorphic on fixed small punctured disks. Continue to a fixed ordinary point, e.g. z=1/2, along a fixed path avoiding singularities. Standard holomorphic dependence for a first-order linear system gives jointly holomorphic values and derivatives. The local basis at 1 has nonzero Wronskian; its inverse at the ordinary point therefore yields holomorphic d₁,d₂. Choose one branch of (1−z)^(1−δ) once; the branch choice scales d₂ by a nonzero constant and cannot change its zero germs.

## Simple zero: a necessary exceptional-case check

At s=0, put c=γ+δ−1 and choose a,b with a+b=c and ab=B. The hypergeometric connection formula gives

    d₂(B,0)=Γ(γ)Γ(δ−1)/(Γ(a)Γ(b)).

This expression is symmetric, hence holomorphic in B even when a=b. At B=−D_k, a=−k and b=k+c. For k≥1 the derivative is

    ∂_B d₂(−D_k,0)=Γ(γ)Γ(δ−1)(−1)^k k! / ((2k+c)Γ(k+c)),

and is nonzero under the assumptions. For k=0, the uniformly valid formula is

    ∂_B d₂(0,0)=Γ(γ)Γ(δ−1)/Γ(c+1).

The allowed case c=0 (γ+δ=1) MUST NOT be handled by division by 2k+c. Here a+b=0, ab=B and 1/(Γ(a)Γ(b))=B+O(B²), so the zero is still simple. Thus the analytic implicit function theorem provides the genuine convergent zero germ B_k(s).

## Why the formal polynomial jets belong to the analytic zero germ

For each J use the polynomial parameter jet B^{≤J}(s)=−D_k−Σ_{j=1}^J λ_j s^j, and let u(z,s) be the genuine normalized solution at zero for this parameter. Uniqueness of the inhomogeneous Taylor recurrence at zero proves that its s-jets through J are exactly p_j(z). Analytic continuation along the fixed path preserves that equality. In particular, those jets are polynomials and therefore regular at z=1.

Expand the connection identity u=d₁u₁+d₂u₂ in s, where u₁ is regular at 1 and u₂=(1−z)^(1−δ) times a regular function with nonzero constant term. Suppose the first nonzero coefficient of d₂ occurs at order h≤J. At that order, all derivatives of d₂ of lower order vanish, so the only nonregular contribution is the nonzero scalar [s^h]d₂ times u₂(z,0). Everything else is regular at 1. This contradicts the polynomial nature of p_h because δ is not an integer. Hence d₂(B^{≤J}(s),s)=O(s^{J+1}). Simplicity of its B-zero implies that B^{≤J} is the J-jet of B_k. This avoids interchanging an infinite coefficient limit with parameter derivatives and requires no uniform Darboux theorem.

## Identification with finite recurrence roots

Since deg p_j≤k+j, for N≥k+J+1 the coefficient of z^N in u(z,s) is O(s^{J+1}). Thus c_N(B_k(s),s)=O(s^{J+1}). The finite polynomial c_N(B,0) has a simple root at −D_k, so its zero germ agrees with B_k through order J. Choose N=k+J+1 and invoke the source's Proposition 4.7 for lower orders. This gives exactly λ_J=D_k^{[J],(k+J+1)} and proves (4.30).

## Corpus attribution and limits

Gcoy's equation-module / operator-word / solution-functor viewpoint motivates tracking finite polynomial jets rather than truncating the global connection itself. The actual mechanisms used here—triangular polynomial operators, formal perturbation, Frobenius theory, and the implicit function theorem—are classical and are proved or explicitly invoked above; no unsupported Gcoy axiom is needed.

The corpus's blanket suggestion that monodromy is simply exp(2πi residue) must not be used in resonant cases. For example y′=(diag(1,0)/z+E₁₂)y has solutions y₂=C₂, y₁=z(C₁+C₂ log z), so its monodromy is nontrivial although exp(2πi residue)=I. Nor are general Heun accessory constraints finite algebraic equations. These issues do not affect the present nonresonant analytic argument.
