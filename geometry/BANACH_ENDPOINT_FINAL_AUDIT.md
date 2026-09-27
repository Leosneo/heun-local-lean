# Endpoint and analytic-continuation audit

Date: 2026-09-27. Read-only audit of the Lean source definitions and the checked
BanachODE / BanachEndpoint proofs.

## Findings

No mathematical gap found in the endpoint bridge.

1. `fast_series_analytic` proves analyticity of the actual sum on the open disk
   |z|<2 from the coefficient bound C·2^(-n). Its local uniform bound is taken
   on an intermediate radius strictly between |z| and 2. There is no claim of
   convergence on the boundary |z|=2.
2. The continued expression is `equationValue`, the polynomial-cleared
   differential expression. This is analytic at both endpoints. Its vanishing
   near zero comes from the actual coefficient recurrence and summable first
   and second derivative series. The identity principle on the connected disk
   extends this cleared identity, without asserting rational coefficients are
   analytic across their poles.
3. The rational ODE is recovered only where z≠0 and z≠1. Its moving denominator
   1-sz is explicitly nonzero: |s|≤1/1000 and |z|<2 imply |sz|<1. Thus the Heun
   moving singularity does not enter the disk. The confluent and reduced cases
   also satisfy the checked identities.
4. The endpoint-one disk |z-1|<3/4 lies in |z|<7/4<2 and excludes zero. The
   solution is analytic on the entire endpoint disk and satisfies the rational
   ODE on that disk with the endpoint removed.
5. The regular endpoint solution is u(z)=y(z)/y(1), with y(1)≠0 proved by the
   quantitative estimate |Σ decode(x)-Σ decode(v)|≤2‖x-v‖ and the established
   nonzero base polynomial endpoint value. The singular factor is the already
   constructed actual normalized Frobenius factor, not an unspecified witness.
6. The resulting relation is exactly the existing `IsConnectionCoefficient`
   definition, using y(0)=1, u(1)=1, h(1)=1 and the principal complex-power
   connection identity on the overlap. Its singular coefficient is zero.
7. Uniqueness of that coefficient is independently proved across all choices
   of normalized witnesses. It uses an endpoint halfdisk that reaches one;
   it does not use the fixed overlap as an approach filter at one.

## Scope

The conclusion is a local analytic accessory-parameter branch for every fixed
admissible complex parameter tuple, every nonnegative integer k, and each of
three stated equation families. The positive parameter radius may depend on
those fixed data and k. The proof may shrink it to ≤1/1000 internally.

It does not assert a common radius for all parameters/k, global continuation in
s, completeness of all connection zeros away from the base point, or convergence
at the chosen radius boundary. Nor does it prove the connection zero is simple
as a function of accessory parameter; the Banach bordered inverse avoids that
previously missing Gamma-formula route. Uniqueness of the scalar connection
coefficient for fixed B,s is distinct from global uniqueness of connection roots.

The final source `HeunCompletion.lean` was subsequently inspected. Its theorem
`literatureConjecture : LiteratureConjecture` obtains finite analytic roots from
`finite_root_germ_exists`, the actual analytic encoded branch from the checked
bordered inverse and implicit-function theorem, and the exact convergent series
from `final_hasSum_of_encoded_branch`. It intersects the Taylor convergence and
endpoint connection neighborhoods and uses the independent connection uniqueness
theorem. No missing simplicity assumption is reintroduced. The parent reports
successful compilation with only propext, Classical.choice, and Quot.sound; the
full rebuild remains the final reproducibility check.
