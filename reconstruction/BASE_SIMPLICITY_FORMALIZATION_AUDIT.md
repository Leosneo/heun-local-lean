# Base connection simplicity: dependency audit, 2026-09-27

## Reusable Lean literature search

The pinned mathlib's `Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`
provides coefficients, symmetry, termination and convergence radius. It does
not provide Gauss evaluation, Euler integral or a connection formula.

Current upstream documentation adds `RegularizedHypergeometric.lean`:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.html
Its published theorem list provides generalized coefficients, radius,
analyticity in the disk, and the normalization identity
`ordinaryHypergeometric_div_Gamma_eq`. It likewise does not supply a Gauss
connection formula. This new module is absent from our pin, so importing it
would not itself close the gap.

GitHub code search (queries `hypergeometric connection`, `ordinaryHypergeometric Gamma`,
`Gauss hypergeometric`, and repository-focused follow-ups) found no reusable
proved general connection formula. Relevant inspected results:

- https://github.com/jaumededios/LMLF/blob/00f4ab46c750d006319066f44115a218c1cc4c62/blueprint/families/hypergeometric_legendre.md
  treats integral representations and connection formulas as planning work.
- https://github.com/jaumededios/LMLF/blob/00f4ab46c750d006319066f44115a218c1cc4c62/LMLF/Definitions/Hypergeometric.lean
  wraps local series and Gamma normalization, not endpoint continuation.
- https://github.com/Vilin97/lean-pool/blob/6c348222a322bed75a31075a776d5aa004ea40b8/LeanPool/Chudnovsky/Kummer.lean
  concerns the modular/hypergeometric relation in a Chudnovsky proof; search
  did not identify a general Gauss endpoint connection formula there.

This is a bounded search conclusion, not proof that no such code exists.

## Direct simplicity proof: why the obvious reductions do not finish it

At the polynomial eigenvalue B=-D_k, if the accessory derivative of the
connection determinant vanished, differentiating the normalized solution
would produce a generalized eigenfunction regular at both 0 and 1.
Polynomial spectral simplicity rules this out only AFTER proving that such
a regular generalized eigenfunction lies in the polynomial class. That
bridge is not automatic: local regularity on two overlapping disks is not
polynomiality. A global continuation/growth or Jacobi pairing argument is
still needed. Do not replace this bridge by an assumption.

A Jacobi weighted pairing can evaluate the obstruction with beta integrals,
but for the full complex parameter assumptions it needs meromorphic
continuation or a Pochhammer contour. Positivity for real parameters alone
is insufficient for the paper's full theorem.

## Alternative construction avoiding the base connection formula

Possible new route, NOT yet formalized:

1. Fix R>1 and use the Banach domain of sequences with norm
   sum_n (1+n^2)|c_n|R^n, with target norm sum_n |a_n|R^n.
2. In the monomial basis the unperturbed polynomial differential operator
   has diagonal D_n-D_k and a lowering entry proportional to n(n-1+gamma).
3. After dividing by the diagonal on a sufficiently high tail, lowering
   has norm tending to 1/R<1. A Neumann inverse handles the infinite tail;
   the finite head has exactly one resonance, at k.
4. Adjoin the accessory parameter variation and impose c_0=1. The
   eigenpair linearization should then be invertible because the kernel
   is the normalized degree-k polynomial and D_n are distinct.
5. The perturbation operator raises polynomial degree by at most one and
   has coefficients O(n^2), so it is bounded from this domain to target.
   Banach analytic IFT would construct an actual analytic eigenpair.
6. Its solution is analytic on |z|<R and therefore across both 0 and 1.
   It supplies a connection-zero branch without needing the Gamma formula.

All operator estimates, spaces, invertibility and the link to the exact
endpoint definition would need Lean proofs. This is a plausible alternate
workstream, not a completed result or a replacement theorem.
