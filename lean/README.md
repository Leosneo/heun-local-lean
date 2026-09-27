# Heun conjecture: completed local Lean formalization

The literal local conjecture is implemented in `HeunProblem.lean` as
`Heun.LiteratureConjecture`. **It is proved by `Heun.literatureConjecture` in
[HeunCompletion.lean](HeunCompletion.lean).**

The complete theorem compiles with axiom dependencies exactly
`[propext, Classical.choice, Quot.sound]`. There are no `sorry` placeholders
or added mathematical axioms. The proof uses the bounded-sequence eigenpair
construction below; it does not assume the Gamma connection formula or
simplicity of the actual connection zero.

## Fidelity to the literature

Source: Mori–Takemura, *On zeros of polynomials associated with Heun class
equations*, [arXiv:2503.10355v3](https://arxiv.org/html/2503.10355v3),
equations (3.5), (3.11), (3.15), (4.1), and Conjecture 1 / (4.30).

The implementation includes:

- All three actual complex differential equations, using complex derivatives.
- The stated noninteger endpoint parameters, noncolliding unperturbed
  eigenvalues, and the Heun parameter balance.
- The actual three-term coefficient recurrence with the source's D, E, F.
- The finite-root germs and their Taylor coefficients, with the source's signs
  and index `k+j+1`.
- The connection coefficient specified through actual normalized analytic
  solutions at zero and one, and the identity
  `y = d₁*u + d₂*(1-z)^(1-delta)*h` on their overlap.
- Existence of the connection-zero branch and convergence of its specified
  series as conclusions of the target, not assumptions.

The relation `IsConnectionCoefficient` specifies the connection independently
of a choice of endpoint solutions. `ActualConnection.lean` constructs a
coefficient satisfying this relation, and `ConnectionUniqueness.lean` proves
its uniqueness. It is not defined to be zero, defined from an unproved limit,
or identified by definition with the conjectured series.

Endpoint disks have radius 3/4. The target restricts to a sufficiently small
parameter disk of radius less than 1/4, which is legitimate for the local
conjecture and keeps the moving Heun singularity away. The overlap avoids the
principal power's branch cut. The convergence radius can depend on k.

## Checked mathematical components

The following results have compiler-checked proofs. None assumes the
literature conjecture or inserts the missing connection simplicity as an axiom.

| Files | Proven content |
|---|---|
| `HeunProblem`, `OperatorBridge`, `PolynomialGrammar` | Exact source definitions and recurrence; polynomial operators equal the rational complex ODE; all three perturbations raise degree by at most one |
| `BaseEigenfunction`, `BaseAnalytic` | Constructed normalized eigenpolynomials of exact degree k; nonvanishing at endpoint one; actual analytic base endpoint solutions |
| `PerturbationJets` | Polynomial eigenbasis, reduced inverse, and recursively constructed normalized perturbation coefficients at every order, with degree at most k+j |
| `FiniteRoot`, `Integration`, `FiniteRootUniqueness` | Actual finite analytic root existence, uniqueness as a germ, and independence of Taylor coefficients from the representative |
| `FiniteRootStabilization`, `AnalyticTaylorBridge` | All-order stabilization for the exact formal recurrence, transferred to the actual analytic finite-root derivatives and the literature's `finiteRootTaylor` |
| `FrobeniusBounds` | Uniform geometric coefficient bound for complex B and s; requires only gamma nonresonance |
| `FrobeniusAnalytic`, `FrobeniusODE` | Absolute convergence on the disk of radius 4/5; analyticity; termwise first and second derivatives; normalized actual solution of each source ODE near zero |
| `FrobeniusTransform`, `FrobeniusGauge`, `FrobeniusOne`, `SingularSolution` | Checked reflection and exponent-shift identities; constructed normalized regular and singular Frobenius solutions at endpoint one; singular solution verified on the slit endpoint disk |
| `BaseConnection` | The literal relation `IsConnectionCoefficient f p (-D p k) 0 0` under the literature assumptions |
| `SingularGerm` | Actual noninteger complex powers, including the normalized endpoint singular factor, cannot extend analytically through the endpoint |
| `CauchyBounds`, `JointAnalytic` | Parameter derivative estimates and genuine joint complex C1 dependence of the series and its z-derivative; complex C1 implicit equations with invertible accessory derivative give analytic scalar root branches |
| `ODEUniqueness` | Ordinary-point analytic ODE uniqueness; a pair with nonzero Wronskian spans analytic solutions on a connected common domain |
| `RegularSingularUniqueness`, `ConnectionUniqueness` | Uniqueness of the normalized source solution at zero and of the literal connection coefficient across all allowed Frobenius witnesses |
| `EndpointIndependence`, `ActualConnection` | Independence of the regular and singular endpoint germs; nonzero midpoint Wronskian; existence of the actual connection coefficient and its explicit Cramer formula |
| `ConnectionAnalytic` | Genuine joint complex C1 dependence of that actual connection coefficient on B and s |
| `BanachSpace`, `BanachOperators` | Complete bounded-sequence space, weighted coefficient decoding, actual bounded Heun operators, and eventual contracting-tail estimates |
| `BanachInverse`, `BanachHead`, `BanachInvertible` | Neumann inverse for the infinite tail, finite-prefix extension, resonant finite-head solution, and invertibility of the concrete bordered Heun operator |
| `BanachBranch` | Analytic Banach-valued eigenpair from the actual implicit equation |
| `BanachODE`, `BanachRecurrence`, `BanachEndpoint` | Radius-two analyticity, exact source recurrence and ODE, and the genuine endpoint connection-zero condition |
| `FinalAssembly` | Polynomial support of every actual branch jet, identification with finite-root Taylor coefficients, and the exact convergent `HasSum` |
| `HeunCompletion` | Complete proof of `Heun.LiteratureConjecture`, with all substantive hypotheses discharged from `Admissible` |
| `BanachTail` | Earlier auxiliary weighted-tail estimate; not needed for the final theorem |
| `AnalyticBridge`, `JetPropagation` | Supporting analytic-germ and recurrence lemmas |

## Completed argument and scope

The normalized sequence coordinate is

```
x_n = (n+1)^2 * 2^n * c_n.
```

Bounded coordinates define an analytic solution on `|z|<2`, containing both
fixed endpoint disks. The actual source equation becomes a bounded operator
equation. Its linearization, bordered by the accessory parameter and the
normalization `c_0=1`, is invertible: the high tail is a contracting shift,
and the finite head has exactly one resonant row, which determines the
accessory variation. The complex implicit-function theorem then supplies
an analytic bounded-sequence branch.

The branch solves the literal recurrence and ODE, remains nonzero at endpoint
one, and therefore has actual connection coefficient zero. Differentiating
the recurrence and using bounded-tail uniqueness proves that the order-j
solution jet has degree at most k+j. These jets identify the branch's Taylor
coefficients with the finite roots at precisely the source's truncation
indices. Scalar analyticity supplies the final convergent series.

The theorem is local for each fixed k and admissible parameter tuple. It
proves neither a radius uniform in k, global spectral enumeration, nor
extension to resonant parameters. It does not prove the separate assertion
that the connection zero is simple in the accessory parameter. The earlier
Gamma-formula route remains unformalized, but is no longer an obligation
of this completed proof.

The earlier weighted-ℓ¹ mathematical proposal is recorded in
`../reconstruction/BANACH_EIGENPAIR_ROUTE.md`. The checked implementation
uses normalized bounded sequences instead. The independent inverse and
endpoint audits are in `../arithmetic/BANACH_INVERSE_AUDIT.md` and
`../geometry/BANACH_ENDPOINT_FINAL_AUDIT.md`. No priority or peer-review
claim follows from compilation.

## Existing library reuse

The earlier bounded search missed external Frobenius developments. Ripple has
substantial real regular-singular series theory, and jjmath has complex
ordinary-point ODE machinery. See `../geometry/GITHUB_FROBENIUS_SEARCH.md`.
The present Heun-specific convergence and ODE proofs were implemented directly
against the pinned mathlib. No claim is made that Frobenius theory was absent
from all existing Lean projects.

## Reproduction

From the repository root run `lake exe cache get`, then `sh check.sh`.
Lean and mathlib are pinned by the root toolchain, Lake configuration, and
lockfile. See the root README for scope and installation instructions.
