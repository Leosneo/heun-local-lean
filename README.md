# Local Heun connection-root expansions in Lean

A Lean formalization of local convergent connection-zero branches for the
Heun, singly confluent Heun, and reduced singly confluent Heun equations.

## What is proved—and what is not

For every fixed admissible complex parameter tuple and natural number k,
there is a positive radius on which an actual endpoint connection zero has
the convergent expansion

```text
B_k(s) = -D_k - Σ_{j≥1} D_k^[j],(k+j+1) s^j.
```

The coefficients come from the actual finite recurrence roots; the connection
coefficient is defined using actual normalized analytic ODE solutions.
The theorem is `Heun.literatureConjecture : Heun.LiteratureConjecture` in
[HeunCompletion.lean](lean/HeunCompletion.lean).

**Scope limitation:** this constructs a local zero branch for every k. It does
not prove that these branches exhaust every connection zero, does not provide
a convergence radius uniform in k, and does not prove global continuation.
The name `LiteratureConjecture` denotes the explicit local proposition in
[HeunProblem.lean](lean/HeunProblem.lean); it should not be read as a claim that
all interpretations of the paper's wording have been proved. In particular,
the converse “every zero belongs to this list” is not formalized here.

The motivating source is Mori–Takemura, [On zeros of polynomials associated
with Heun class equations, arXiv:2503.10355v3](https://arxiv.org/html/2503.10355v3),
Conjecture 1, equation (4.30). Whether its wording additionally intends a
complete enumeration requires a separate argument. No priority or external
peer-review claim is made.

## Proof and files

- [Informal proof matching the formalized route](INFORMAL_PROOF.md).
- [Exact Lean definitions](lean/HeunProblem.lean).
- [Final theorem and assembly](lean/HeunCompletion.lean).
- [Module guide](lean/README.md).
- [Definition/compilation assessment](lean/ASSESSMENT.md).
- [Recorded verification output](lean/assessment_full_build.log).
- [Earlier Gamma-based research draft](HEUN_CONNECTION_ROOT_THEOREM.md).
- `arithmetic/`, `geometry/`, `reconstruction/`: research and audit records.

The original 43 Lean source files are preserved unchanged. Some research
notes record intermediate, incomplete routes or stronger informal claims.
Their presence is not a claim that every statement in those notes has been
formalized. This README and the final Lean theorem specify the verified scope.

The proof constructs a bounded-sequence inverse and applies a complex
implicit-function theorem. It does not rely on an unproved Gamma connection
formula. The final theorem's transitive axiom list is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

There are no `sorry` placeholders or added mathematical axioms.

## Build

Install Lean's `elan` toolchain manager, then from the repository root run:

```sh
lake exe cache get
sh check.sh
```

The committed configuration pins Lean **v4.29.1** and mathlib commit
**5e932f97dd25535344f80f9dd8da3aab83df0fe6**. The lockfile also pins
transitive dependencies. `check.sh` builds the Lean library and rechecks the
final theorem, printing its axiom dependencies.

For a direct incremental build use `lake build`. For the optional finite
symbolic checks, use `python3 check_jets.py` (standard library only).

Recorded on the original arm64 host with already-compiled mathlib: all 43
project modules rebuilt in 191.947 seconds; the final theorem alone recompiled
in 4.194 seconds. These are historical measurements, not fresh-install or
mathlib-build timings. See [timing data](lean/assessment_timings.json).

Compiled Lean artifacts, dependency checkouts, and local caches are excluded
from Git.
