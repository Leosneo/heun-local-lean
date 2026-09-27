# Independent final-statement audit

Audit date: 2026-09-27. Read-only review of `HeunCompletion.lean`, the target definitions in `HeunProblem.lean`, the Banach modules, endpoint bridge, and final Taylor assembly.

## Source fidelity

Primary source freshly opened: [Mori–Takemura, arXiv:2503.10355v3](https://arxiv.org/html/2503.10355v3), Conjecture 1, equation (4.30).

The three encoded equations agree with (3.5), (3.11), (3.15), and their coefficient recurrence agrees with (4.1). The source uses noninteger gamma and delta for the normalized endpoint bases. Section 4 explicitly assumes distinct D indices, equivalently gamma+delta outside the nonpositive integers. The Heun Fuchs relation is part of its definition. These are precisely the formal admissibility restrictions. The finite-root sign and index k+j+1 match (4.6) and (4.30).

The checked target is the **local, per-k convergent expansion**: for every fixed admissible parameter choice and k, a positive radius exists on which the specified stabilized series converges to an actual connection zero. The target does not assert a radius uniform in k, a global enumeration at arbitrary s, or simplicity of the connection function's zero as a separate conclusion. Describe the result with this local scope.

## No vacuity or assumed conclusion found

Admissibility is nonempty. For example, gamma=delta=1/2, alpha=beta=1, epsilon=2 satisfies the Heun conditions. No extra positivity, reality, smallness of fixed exponents, or bound on k appears in the final theorem.

`LiteratureConjecture` quantifies over all three families and all natural k. Finite root germs, an analytic accessory branch, a strictly positive convergence radius, an actual endpoint connection identity with singular coefficient zero, uniqueness of that coefficient, and the infinite-series `HasSum` assertion are conclusions.

`IsConnectionCoefficient` is defined by normalized analytic solutions of the literal ODE and an identity on a nonempty overlap. It is not defined by the stabilized series. Its uniqueness theorem was proved using normalized regular singular uniqueness and noninteger singular-germ nonextension. The singular basis function is actually constructed, not left as an unfulfilled premise.

## Dependency audit

* The Banach inverse's generic tail assumptions are instantiated using actual coefficient limits and the literal base polynomial. The final inverse theorem has only `Admissible` as a mathematical hypothesis.
* The implicit-function theorem receives that concrete inverse and a proved base-kernel identity. It constructs an analytic bounded-sequence branch; no analytic eigenbranch is assumed.
* `residual_coefficients` proves equality with the source recurrence using nonzero recurrence denominators. Its sign is B=-D_k+b.
* The coefficient bound from the normalized sequence yields a spatial radius exceeding both fixed endpoint disks. Nonzero evaluation at one follows from the base polynomial and continuity. The endpoint connection-zero bridge is therefore genuine.
* Polynomial support of all parameter jets is derived from differentiated recurrence and actual bounded-tail uniqueness. It is not an input to the final theorem.
* Finite-root derivative agreement follows from residual vanishing and the proved formal difference unit. This identifies the actual branch's Taylor series with the stated stabilized coefficients.
* The final radius is the minimum of two strictly positive radii. Hence the concluding ball is not empty or reduced to an empty strict-radius condition.

Verdict: no mathematical assumption leak, circular definition, sign/index mismatch, or vacuity was identified. The advertised scope should remain the local convergent-series assertion. Successful kernel compilation and the final axiom audit remain the authority for formal completion.
