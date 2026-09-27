# Direct Banach-space eigenpair construction

**Formalization update, 27 September 2026:** the local literature target is
now proved by `Heun.literatureConjecture` in `../lean/HeunCompletion.lean`.
The checked implementation uses normalized bounded sequences (weighted
ℓ∞ coordinates), rather than the weighted ℓ¹ realization described below.
The status statements below concern this earlier ℓ¹ proposal specifically;
they do not indicate a remaining gap in the completed theorem.

**Status:** complete mathematical route, with explicit operator inverse and estimates; **not a completed Lean formalization**. This avoids the Gauss connection formula and avoids assuming simplicity of an analytic connection determinant. Classical Banach analytic implicit-function and local nonresonant Frobenius theorems are used explicitly below. Existing Lean modules establish many coefficient, jet and Frobenius ingredients, but not the Banach operator construction in this document.

## 1. Exact recurrence and assumptions

Fix one of the three source families, its admissible complex parameters, and k≥0. Put Σ=γ+δ and

    D_n = n(n−1+Σ),    d_n = (n+1)(n+γ),    B₀=−D_k.

Use exactly the source E_n,F_n:

| Family | E_n | F_n |
|---|---|---|
| Heun | n(n−1+γ+ε) | (n−1+α)(n−1+β) |
| Confluent | n | n−1+α |
| Reduced | 0 | 1 |

With c_{−1}=0, the normalized solution recurrence is

    d_n c_{n+1} − (B+D_n)c_n − s E_n c_n + s F_n c_{n−1} = 0,
    c_0=1.                                                 (1)

The source assumptions imply d_n≠0 and D_n≠D_k for n≠k. Indeed, D_n−D_k=(n−k)(n+k−1+Σ), and n+k−1 is a nonnegative integer when n≠k. Let p be the normalized degree-k polynomial coefficient sequence determined by (1) at B=B₀,s=0. Then

    p_0=1,
    p_j= ∏_{i<j}(D_i−D_k)/d_i   (0≤j≤k),
    p_j=0                       (j>k).

In particular p_k≠0, including p_0=1 when k=0.

## 2. Banach spaces and bounded operators

Choose any fixed R>7/4, for example R=2. Define complex Banach spaces

    Y_R = {c : Σ_{n≥0}|c_n|R^n < ∞},
    X_R = {c : Σ_{n≥0}(n+1)^2|c_n|R^n < ∞}.

The displayed sums are their norms. They are weighted ℓ¹ spaces, hence complete, and the inclusion X_R→Y_R has norm at most 1. The closed subspace

    X_R^0 = {h∈X_R : h_0=0}

is Banach. Give X_R^0×ℂ the sum norm. Each coordinate is bounded: |c_n|≤R^(−n)‖c‖_Y and |c_n|≤(n+1)^(−2)R^(−n)‖c‖_X.

Define

    (A h)_n = a_n h_n + d_n h_{n+1},   a_n=D_k−D_n,
    (V h)_n = −E_n h_n + F_n h_{n−1}.

Both map X_R continuously to Y_R. Explicit adequate bounds are

    ‖A‖ ≤ |D_k|+1+|Σ−1|+(1+|γ|)/R,
    ‖V‖ ≤ C_E+R C_F,

where

| Family | C_E | C_F |
|---|---|---|
| Heun | 1+|γ+ε| | (1+|α|)(1+|β|) |
| Confluent | 1 | 1+|α| |
| Reduced | 0 | 1 |

For A, |a_n|≤(|D_k|+1+|Σ−1|)(n+1)^2, and, on reindexing m=n+1,

    |d_{m−1}|≤(1+|γ|)(m+1)^2,
    R^(m−1)=R^m/R.

For V, |E_n|≤C_E(n+1)^2 and |F_{m+1}|≤C_F(m+1)^2. Reindexing the raising term contributes exactly R. No unbounded differentiation operator on Y_R is being silently used; its domain is X_R.

## 3. Explicit inverse of the full linearization

The linearization that must be inverted is

    T : X_R^0×ℂ → Y_R,
    T(h,b)=A h−b p.                                      (2)

We prove it is a bounded linear bijection with a bounded inverse by an explicit construction. No Fredholm assertion or analytic spectral simplicity is assumed.

### 3.1 Uniformly invertible high tail

Set α_R=(R+1)/2 and q=α_R/R<1. Choose an integer L with

    L≥k+1,  L≥1,
    L≥4|Σ−1|,  L²≥4|D_k|,
    L>|Σ|+|D_k|+1,
    (α_R−1)L ≥ |γ|+α_R|Σ|+α_R|D_k|.

Such an integer exists. For n≥L,

    |a_n| ≥ n²−|Σ−1|n−|D_k| ≥ n²/2,
    (n+1)²/|a_n| ≤ 8.                                  (3)

Moreover, putting t_n=d_n/a_{n+1},

    |t_n|
      ≤ (n+|γ|)/(n−|Σ|−|D_k|/(n+1))
      ≤ α_R.                                            (4)

The denominator is positive by the choice of L. The last inequality follows by rearranging the last displayed condition on L and using |D_k|/(n+1)≤|D_k|.

Let Y_tail be weighted ℓ¹ on indices n≥L. Define (S u)_n=t_n u_{n+1}. Then

    ‖S u‖_tail ≤ (α_R/R) ‖u‖_tail = q‖u‖_tail.

The missing n=L term when shifting the sum only improves the inequality. Consequently

    (I+S)^−1 = Σ_{j≥0}(−S)^j,
    ‖(I+S)^−1‖ ≤ 1/(1−q).                              (5)

For arbitrary y∈Y_R, put

    u=(I+S)^−1(y|_{n≥L}),    h_n=u_n/a_n  (n≥L).

Then a_n h_n+d_n h_{n+1}=y_n on the tail, and (3)–(5) give

    Σ_{n≥L}(n+1)²|h_n|R^n ≤ 8‖y‖_Y/(1−q).              (6)

This is the unique X-tail solution: any such h gives u_n=a_n h_n∈Y_tail because |a_n|/(n+1)² is bounded, so (I+S)u=y and (5) applies.

### 3.2 Finite downward propagation and resonance equation

For n=L−1,L−2,…,k+1, define

    h_n=(y_n−d_n h_{n+1})/a_n.

Every denominator is nonzero. These coefficients are independent of b because p_n=0 for n>k. The equation at n=k now determines b uniquely:

    b=(d_k h_{k+1}−y_k)/p_k.                            (7)

At this point h_k is still free. Define a particular finite head by

    t_k=0,
    t_n=(y_n+b p_n−d_n t_{n+1})/a_n   (n=k−1,…,0).

Set

    h_n=t_n−t_0 p_n   (0≤n≤k).                          (8)

Since p_0=1, (8) gives h_0=0. Since A p=0, all equations at n<k hold. At n=k the coefficient a_k vanishes, so (8) does not disturb (7). Thus T(h,b)=y.

For k=0, the head recursion is empty, t_0=0, and (8) simply imposes h_0=0. Formula (7) remains valid with p_0=1. No exceptional k=0 case is omitted.

Uniqueness follows in the same order: zero data force zero tail, then zero coefficients down to k+1, then b=0 by p_k≠0. The remaining head is a multiple of p, and h_0=0 forces that multiple to vanish.

### 3.3 Explicit boundedness of the inverse

All constructions are complex linear. Here are finite constants that make continuity completely explicit. Start with

    H_L=R^(−L)/(|a_L|(1−q)).

For n=L−1,…,k+1, set

    H_n=(R^(−n)+|d_n|H_{n+1})/|a_n|.

Then |h_n|≤H_n‖y‖. Set

    C_b=(|d_k|H_{k+1}+R^(−k))/|p_k|.

Thus |b|≤C_b‖y‖. Put Q_k=0 and recursively

    Q_n=(R^(−n)+C_b|p_n|+|d_n|Q_{n+1})/|a_n|
         (n=k−1,…,0).

Then |t_n|≤Q_n‖y‖ and |h_n|≤(Q_n+Q_0|p_n|)‖y‖ for n≤k. Together with (6), an explicit inverse bound is

    ‖T^−1‖ ≤ C_b + 8/(1−q)
      + Σ_{k<n<L}(n+1)²R^n H_n
      + Σ_{0≤n≤k}(n+1)²R^n(Q_n+Q_0|p_n|).              (9)

Empty sums are zero. These constants are finite and depend only on fixed parameters,k,R,L.

## 4. Analytic implicit-function theorem

Define the map ℂ×(X_R^0×ℂ)→Y_R by

    Φ(s,h,b)=A h−b p−b h+s Vp+s Vh.                    (10)

This is a continuous polynomial map between complex Banach spaces and therefore analytic. Here b h uses the bounded inclusion X_R→Y_R. We have Φ(0,0,0)=0, and its derivative in (h,b) at zero is exactly the bounded isomorphism T in (2).

The analytic Banach implicit-function theorem therefore gives analytic maps h(s)∈X_R^0 and b(s)∈ℂ near s=0, with h(0)=0,b(0)=0, such that Φ(s,h(s),b(s))=0. Put

    c(s)=p+h(s),    B(s)=−D_k+b(s).

Equation (10) is exactly (1), and c_0(s)=1. The source recurrence has nonzero d_n, so its unique normalized coefficients equal c_n(s) at every n.

The function

    y_s(z)=Σ_{n≥0}c_n(s)z^n

is analytic on |z|<R. Evaluation of y, y′ and y″ on each strictly smaller disk is bounded on X_R; for example their coefficient bounds involve 1, n/R and n(n−1)/R², dominated by the chosen (n+1)² weight. Termwise substitution proves the exact source ODE away from its singularities. Shrink the s-neighborhood so |s|R<1 in the Heun case. The extra singularity 1/s then lies outside the disk. There is no assertion of a radius uniform in k.

## 5. Exact endpoint connection-zero statement

Because R>7/4, both fixed disks in `HeunProblem.lean` (radius 3/4 about 0 and 1) lie in |z|<R. Thus y_s is regular across both endpoints.

First p(1)≠0. If p had a zero of order m≥1 at z=1, the lowest term of the s=0 ODE, after multiplying out its regular-singular denominator, would have coefficient proportional to m(m−1+δ). This is nonzero because δ is not an integer. Contradiction. Since p is nonzero (p(0)=1), p(1)≠0. This elementary local argument avoids Chu–Vandermonde. Bounded evaluation and continuity imply y_s(1)≠0 for small s. Set

    u_s(z)=y_s(z)/y_s(1),    d₁(s)=y_s(1),    d₂(s)=0.

Then u_s is analytic on the one-disk, normalized by u_s(1)=1, and solves the same ODE.

The definition `IsConnectionCoefficient` also asks for a normalized singular Frobenius solution. Its independent local existence is supplied by the ordinary nonresonant Frobenius construction. For clarity, it can be reduced exactly to the same normalized recurrence at w=1−z, followed by the gauge w^λ with λ=1−δ:

| Family | First change w=1−z |
|---|---|
| Heun | γ′=δ, δ′=γ, s′=s/(s−1), B′=(B−sαβ)/(1−s), α′=α,β′=β,ε′=ε |
| Confluent | γ′=δ, δ′=γ, s′=−s, B′=B−sα, α′=α |
| Reduced | γ′=δ, δ′=γ, s′=−s, B′=B−s |

For H(w)=w^λ h(w), the analytic h-equation has γ″=2−δ and δ″=γ. The remaining changes are:

| Family | Gauge-transformed data |
|---|---|
| Heun | α″=α+λ, β″=β+λ, ε″=ε, B″=B′+λγ+λs′ε |
| Confluent | α″=α+λ, B″=B′+λγ+λs′ |
| Reduced | B″=B′+λγ |

The perturbation remains s′. The Heun simplification uses the source Fuchs relation. Since δ is noninteger, γ″ is not a nonpositive integer. The normalized h-series exists on a disk containing |w|<3/4 for sufficiently small s by the already available recurrence convergence estimates (or classical Frobenius convergence). With h_z(z)=h(1−z), it gives precisely `(1−z)^(1−δ) h_z(z)` on the specified overlap, with h_z(1)=1.

Thus the exact existential `IsConnectionCoefficient f p (B(s)) s 0` holds. Uniqueness of d₂ follows from uniqueness of the normalized regular Frobenius germ and linear independence of regular and noninteger-exponent singular germs. This last independence must be proved, not inferred merely from the chosen representation. In a Lean assembly it belongs to the endpoint/singular-germ module.

## 6. Identification with stabilized finite-root Taylor coefficients

The Banach-space branch is analytic, so write c(s)=Σ_j c^[j]s^j and B(s)=B₀+Σ_{j≥1}b_j s^j. Coefficient extraction in (10) gives, at each order j≥1,

    T(c^[j], b_j)
      = Σ_{1≤i<j} b_i c^[j−i] − V c^[j−1].             (11)

Here c^[0]=p, and c^[j]_0=0. Uniqueness of the inverse T makes every coefficient pair unique once lower orders are fixed.

The inverse constructed above preserves polynomial support in the following precise sense: if y has support ≤d with d≥k, then T^−1 y has h supported ≤d. In fact choose the high-tail cutoff beyond d; zero tail data give zero tail solution by (5), and the downward recursion preserves zero until d. (The construction and uniqueness show the choice of cutoff is immaterial.) Since V increases degree by at most one, induction in (11) gives support(c^[j])≤k+j.

For a finite analytic root b_N(s) with N≥k+J+1, the already Lean-verified `analytic_finite_root_solution_jet_support` says its normalized coefficient jets through order J likewise have support ≤k+j. These finite polynomial jets satisfy (11), by the exact recurrence. They are therefore elements of X_R and, by the same invertible T and induction on j≤J, equal the Banach branch's jets. In particular

    (d/ds)^j b_N(0) = (d/ds)^j B(0)    for 0≤j≤J.

This identification uses no limiting interchange in N and no assertion that the finite root is itself a connection zero.

Hence the stabilized numbers in the paper are precisely minus the Taylor coefficients of the analytic B(s). Their series converges on a sufficiently small disk and sums to the constructed genuine connection-zero branch. This proves the desired mathematical convergence assertion without invoking the Gamma connection formula or an unproved derivative formula for the connection Wronskian.

## 7. Exact remaining Lean work

Already checked: recurrence identities, finite-root analytic existence and uniqueness, Taylor-ring bridge, all-order finite-root stabilization, polynomial jet support, geometric convergence bounds, joint C¹ dependence of y and y′, actual endpoint Frobenius solutions, connection existence and uniqueness, joint C¹ dependence of the actual connection coefficient, and scalar analytic implicit-branch machinery. `BanachTail.lean` also checks the elementary ℓ¹ tail-shift norm estimate.

Not yet checked for this route: weighted ℓ¹ Banach spaces, bounded A/V, the tail shift as a bounded operator and its Neumann inverse, finite-head inverse assembly, the Banach analytic implicit-function specialization, evaluation/ODE bridge for the resulting coefficient sequence, and final branch/Taylor assembly. The estimates and algebra needed for the new central inverse are explicit in §§2–3. This document must not be described as a completed Lean proof.
