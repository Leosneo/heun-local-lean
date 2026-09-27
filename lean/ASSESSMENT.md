# Fresh definition and compilation assessment

Assessment: 2026-09-27T12:16:32+0200.

## Verdict

The implemented statement faithfully expresses the local, per-k convergent
branch assertion in Mori–Takemura's Conjecture 1, equation (4.30).
Fresh compilation of the complete project and the final theorem both passed.

## Definition comparison

Primary source: https://arxiv.org/html/2503.10355v3 .

| Paper item | Lean representation | Assessment |
|---|---|---|
| Equations (3.5), (3.11), (3.15) | `drift`, `potential`, `SolvesOn` | All three complex differential equations agree |
| Endpoint and distinct-eigenvalue assumptions | `Admissible` | Noninteger gamma/delta, noncolliding D values, Heun Fuchs relation agree |
| Recurrence (4.1), initial coefficients | `coefficientPair`, `D`, `E`, `F` | Coefficients, signs, and c[-1]=0, c[0]=1 agree |
| Normalized endpoint connection (3.8) | `IsConnectionCoefficient` | Actual analytic ODE solutions; normalization and singular power agree |
| Finite-root expansion (4.6) | `IsFiniteRootGerm`, `finiteRootTaylor` | Minus sign and factorial normalization agree |
| Expansion (4.30) | `LiteratureConjecture` | Exact k+j+1 index and actual convergent `HasSum` conclusion |

This comparison is a mathematical review, separate from Lean's proof checking.
The overlap is nonempty (it contains 1/2), the convergence radius is strictly
positive, and endpoint existence and uniqueness are proved rather than assumed.

## Scope qualification

For each fixed admissible parameter tuple and k, the theorem constructs a
local analytic connection-zero branch with the stated convergent series.
It does not assert global exhaustion of all connection zeros, a radius uniform
in k, global continuation, or a separate simple-zero theorem. The paper's
wording should therefore be cited as its local expansion assertion, without
silently adding a global enumeration interpretation.

## Fresh compilation

- Lean: Lean (version 4.29.1, arm64-apple-darwin24.6.0, commit f72c35b3f637c8c6571d353742168ab66cc22c00, Release).
- mathlib commit: `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
- Project: 43 Lean files, 6337 lines including comments and audits.
- Final assembly file: 61 lines.
- Full source rebuild via `sh check.sh`: **PASS**, exit 0, **191.947 seconds**.
- Final theorem recompile with compiled dependencies: **PASS**, exit 0, **4.194 seconds**.
- Timing scope: Recompile project sources against existing compiled mathlib; no mathlib rebuild or download.
- Host architecture: arm64; logical CPU count: 10.
- Existing stylistic linter warnings do not prevent compilation; no compiler errors were found.

The final theorem's transitive axiom report is exactly:

```
Heun.literatureConjecture : Heun.LiteratureConjecture
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurs in either fresh log. The project-source scan found no
`sorry`, `admit`, added `axiom`, `unsafe`, `native_decide`, `implemented_by`,
or `Lean.ofReduceBool` occurrences.

Evidence: `assessment_timings.json`, `assessment_full_build.log`,
`assessment_final_theorem.log`. Sources were not modified during measurement.
