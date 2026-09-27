# Informal proof of the verified local statement

This note describes the bounded-sequence route used in the Lean proof. The
claim is local branch existence and convergence for each fixed k. It does
not assert that the constructed branches exhaust all zeros.

## Statement

Fix one of the three Heun families. Assume gamma and delta are not integers,
gamma+delta is not a nonpositive integer, and, in the Heun case,
gamma+delta+epsilon=alpha+beta+1. Define

```text
D_n = n(n-1+gamma+delta),  d_n = (n+1)(n+gamma).
```

The normalized source coefficients obey

```text
d_n c_(n+1) = (B+D_n+s E_n)c_n - s F_n c_(n-1),
c_0=1, c_(-1)=0.
```

The actual E and F for all three families are defined in `lean/HeunProblem.lean`.
For each k we prove a local analytic connection-zero branch through B=-D_k,
whose Taylor coefficients equal the stabilized finite-root coefficients in
the source formula (4.30).

## 1. A complete space that controls both endpoints

Use the Banach space X of bounded complex sequences, with the supremum norm.
Encode coefficients by

```text
x_n = (n+1)^2 2^n c_n,   c_n = x_n / ((n+1)^2 2^n).
```

Then |c_n| is at most ||x|| 2^(-n). Consequently the power series is analytic
on |z|<2, a disk containing both fixed endpoint disks used in the definition
of the connection coefficient.

At s=0 and B=-D_k the recurrence terminates, giving a normalized polynomial
p of degree exactly k. Write pX for its encoded sequence.

## 2. The bounded operator equation

Put B=-D_k+b. Multiplying the recurrence residual by 2^n gives

```text
A x - b J x + s V x = 0,   x_0=1,
```

where A, J, V are bounded linear operators on X. In particular,

```text
(Ax)_n = a_n x_n + beta_n x_(n+1),
a_n = (D_k-D_n)/(n+1)^2,
beta_n = (n+1)(n+gamma)/(2(n+2)^2),
(Jx)_n = x_n/(n+1)^2.
```

The three V operators are exactly the transformed source perturbations.
Their boundedness follows by expressing their coefficients as polynomials
in 1/(n+1), together with bounded forward/backward shifts.

## 3. Invert the complete linearization

The derivative in (x,b) at (pX,0), including normalization, is

```text
T(h,t) = (A h - t J pX, h_0).
```

The diagonal a_n vanishes only at n=k. Moreover a_n tends to -1 and beta_n
tends to 1/2. For all sufficiently large n, inverse diagonal coefficients
are bounded and |beta_n/a_n| is at most 3/4.

On that tail, division by a_n reduces the equation to I+S with ||S||<1.
The convergent Neumann series gives a unique bounded tail solution. The
finitely many remaining nonresonant rows above k are solved backwards.
At row k, the nonzero top coefficient of p determines t uniquely. Starting
from prescribed h_0, the rows below k are solved forwards, since every
beta_n is nonzero. Finite changes preserve boundedness.

Thus T is a bounded linear bijection between Banach spaces. Its inverse is
continuous by the bounded inverse theorem. This supplies the actual inverse
required by the implicit-function theorem; it is not a hypothesis left over
in the final result.

## 4. Construct the analytic branch and actual connection zero

The map (s,x,b) to (A x-b J x+s V x,x_0-1) is a continuous polynomial map.
The complex implicit-function theorem supplies analytic x(s), b(s) near zero.
Decoding x(s) gives exactly the normalized source recurrence coefficients,
by uniqueness of the recurrence. Set B(s)=-D_k+b(s).

Their power series solves the literal differential equation. The Lean proof
extends the cleared analytic equation across the radius-two disk, then divides
only where the rational denominators are nonzero.

The base polynomial is nonzero at z=1: regular-singular uniqueness there
would otherwise force the normalized polynomial to vanish identically.
Continuity of endpoint evaluation preserves this nonvanishing for small s.
Normalize the constructed solution at one by dividing by its value there.
Together with the independently constructed singular Frobenius solution,
this proves the actual connection relation with singular coefficient zero.
Uniqueness of that coefficient follows from the noninteger singular exponent
and normalized regular-singular uniqueness.

## 5. Identify the Taylor series

The order-j derivative of x(s) is still a bounded sequence. Inductively,
differentiating the exact recurrence above degree k+j eliminates every
inhomogeneous lower-order term. The remaining tail solves the homogeneous
unperturbed equation. The proved bounded-tail uniqueness forces it to vanish.
Hence the order-j solution jet has polynomial degree at most k+j.

For any N at least k+j+1, the coefficient c_N along B(s) therefore vanishes
through order j. The finite root of c_N at -D_k is simple, so its analytic
root branch has the same Taylor coefficients through that order. This proves
identification with the precise stabilized finite-root coefficients.

Finally, analyticity of B(s) makes its Taylor series converge on some positive
disk. Intersect this disk with the connection-zero neighborhood. This gives
the literal `HasSum` assertion and endpoint relation in `LiteratureConjecture`.

## Boundary of the conclusion

Every constructed branch is a zero locally. No reverse implication asserting
that every connection zero belongs to one of these branches is proved here.
No positive lower bound uniform in k is asserted for the convergence radii.
