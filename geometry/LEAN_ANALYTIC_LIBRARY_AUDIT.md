# Lean analytic bridge audit

Pinned mathlib commit: `5e932f97dd25535344f80f9dd8da3aab83df0fe6`, Lean `v4.29.1`, in `research/bures_lean_20260927/mathlib`.

## Usable and implemented

`lean/AnalyticBridge.lean` contains proofs, with no new axioms, of:

- analytic implicit-function existence and local uniqueness, using the actual library `ContDiffAt.implicitFunction` at regularity `ω`;
- the submodule of functions analytically extendable to an endpoint when restricted to a specified set/lens;
- the finite convolution obstruction: if every solution jet and regular contribution extends, but the singular solution's zeroth jet does not, all scalar singular-connection coefficients vanish through the specified order;
- the same assertion when the connection identity holds only as a germ along the lens.

The last theorem is the actual algebraic heart of the paper's endpoint-jet comparison. Its assumptions explicitly require the connection convolution identity, regularity of the two regular contributions, and nonextendability of the singular zeroth jet. These are not silently postulated as properties of Heun solutions.

## Missing substantial pieces

The pinned source has `Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`, with the series definition, symmetry, terminating cases and radius results. It does not have the Gauss endpoint connection formula needed to identify and prove simplicity of the base connection zero. No ODE characterization of this hypergeometric function was found there.

No theory of regular-singular Frobenius solutions, analytic dependence of their normalized local bases on accessory parameters, or analytic continuation of such bases along paths was found. The ODE directory contains `Basic`, `Gronwall`, `PicardLindelof`, and `Transform`; the basic integral-curve definitions are real-time ODEs. Those results do not immediately supply the required complex regular-singular theory.

Even with an explicit lens definition of the normalized connection relation, the exact literature theorem still requires existence of the local bases and joint analytic dependence, the hypergeometric base connection computation or an alternative simplicity proof, nonextendability of the noninteger Frobenius power, and compatibility of analytic Taylor coefficients with the formal polynomial-jet recurrence. Defining a relation avoids choosing nonexistent solutions; it does not prove their existence.

## Search scope

Bounded local searches covered `Mathlib/Analysis` for Frobenius, regular singular, hypergeometric, implicit function, and analytic parameter results. A bounded GitHub-indexed web search for mathlib Frobenius ODE, hypergeometric connection formula, and analytic implicit function did not reveal missing implementations. This is not proof that no relevant external Lean project exists.

## Reproduction

From the pinned mathlib directory:

```sh
lake build Mathlib.Analysis.Calculus.ImplicitContDiff
lake env lean <project>/lean/AnalyticBridge.lean
```

The added library dependency was built locally; no packages were installed and no source files in mathlib were changed.
