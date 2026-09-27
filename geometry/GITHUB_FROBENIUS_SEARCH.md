# GitHub Frobenius search — 2026-09-27

This corrects the earlier bounded search: relevant external Lean developments do exist.
This is a source inspection, not a local compilation or transitive axiom audit.

## Ripple: regular-singular polynomial ODE machinery

Source: https://github.com/zinan-huang/Ripple/blob/main/Ripple/Number/Frobenius/Substitution.lean

The inspected file has 8,971 lines and no textual `sorry`, `admit`, or `axiom` occurrences. Its actual theorem statements include:

- `frobeniusSolution_is_solution`: constructs a normalized formal solution under the indicial-root and nonresonance hypotheses.
- `frobeniusCoeff_abs_mul_pow_summable_general`: absolute convergence from explicit coefficient bounds and a simple zero of the leading coefficient.
- `frobeniusValue_analyticOnNhd_general`: analyticity of the resulting sum on a positive real ball.
- `pointwise_ODE_of_analytic_away_from_zero`: converts the coefficient equation into a pointwise ODE identity, with summability and Euler derivative identities as explicit hypotheses.

The inspected statements use real polynomial coefficients, real exponents and real arguments. This is substantial existing Frobenius analysis, not merely terminology or an indicial-polynomial calculation. Adapting it to complex coefficients and establishing joint holomorphic dependence on the Heun parameters remain necessary for our stated target. The simple-zero setup is relevant after clearing the Heun denominators near either finite endpoint, but this application has not been implemented.

Related files:
- https://github.com/zinan-huang/Ripple/blob/main/Ripple/Number/Frobenius/Indicial.lean
- https://github.com/zinan-huang/Ripple/blob/main/Ripple/Number/Frobenius/RegularDisk.lean

`RegularDisk.lean` includes analytic disk gluing, with compatibility supplied explicitly. It does not by itself establish the existence of all continuation disks required for our problem.

## jjmath: complex analytic ordinary-point ODE solutions

Source: https://github.com/quasisphere/jjmath/blob/main/JJMath/Hyperbolic/Schwarzian/Frobenius.lean

The inspected file has no textual `sorry`, `admit`, or `axiom` occurrences. It contains complex coefficient recurrences, geometric majorants, power-series convergence, derivative-series identities and a local normalized solution-pair construction for `y'' + (1/2) q y = 0` with holomorphic coefficient. The final theorem is `holomorphicSchwarzianFrobeniusPairExistence_of_localAnalytic`; its packaged statement uses `LocalSchwarzianData`.

This is useful complex ordinary-point machinery. Its inspected existence theorem does not cover a pole of q at the expansion center, nor does it state joint analytic parameter dependence. Generalizing/extracting these results could support the continuation part of our proof.

## Consequence for the Heun formalization

Do not repeat the blanket claim that Frobenius solution theory has not been formalized in Lean. Existing source can guide or supply portions of the construction, convergence and continuation work. We have not yet verified a directly importable theorem establishing our full parameter-dependent complex Frobenius basis, connection coefficient and endpoint connection formula. The existing Heun conjecture remains unproved in our local Lean development.

Searches used GitHub code search, including `indicial extension:lean`, `"regular singular" extension:lean`, `Frobenius ODE extension:lean`, and Frobenius searches scoped to mathlib4. Search coverage is not exhaustive; default-branch indexing and result limits apply.
