# Independent source and priority audit: Mori–Takemura Conjecture 1

Checked 2026-09-27 against the primary arXiv record and current PDF:
- https://arxiv.org/abs/2503.10355
- https://arxiv.org/pdf/2503.10355v3

The current official version is v3, dated 24 October 2025. Conjecture 1 remains explicitly stated as equation (4.30). Proposition 4.7 ALREADY establishes stabilization of finite-polynomial-root coefficients. The unresolved step is their identification with the connection-zero expansion, including convergence.

The section-wide assumption is pairwise distinct D_j, equivalent to γ+δ not being a nonpositive integer. The connection coefficient is introduced through the nonresonant Frobenius bases, with γ,δ not integers. In the Heun case the connection limit assumes |s|<1; the two confluent cases do not require that restriction.

Exact-title, arXiv-ID, author/conjecture, author/stabilization, and 2026 follow-up searches found no subsequent resolution or journal version. The official record lists no journal reference. Therefore describe this as a published/preprinted research conjecture, not as a verified peer-reviewed publication. The defensible priority language is: “No earlier resolution was found in our targeted search.”

## Independent interpretation and claim boundaries

For each fixed k, the target is the analytic branch passing through (B,s)=(-D_k,0), with its Taylor coefficients specified by finite recurrence data. A proof by local analytic implicit function theorem yields a radius depending on k and the fixed parameters. It must not be reported as a uniform-in-k disk, global entire continuation in s, or classification of every zero for arbitrary nonzero s.

A proof only of finite-jet stabilization would reproduce Proposition 4.7. The new argument must connect those jets to an actual zero of d2, and justify convergence. Passing pointwise coefficient limits through Taylor differentiation without locally uniform control would leave a gap. The team's polynomial-jet plus analytic connection route avoids needing that interchange.

The exact Conjecture 1 is still present in the latest checked primary version. No contradictory later result appeared in the bounded search. Mathematical proof audit is being performed separately by the root and arithmetic/geometry lanes.

## Completed independent proof audit

I subsequently read `arithmetic/HEUN_CONJECTURE_PROOF.md` in full. Verdict: the argument is complete for the stated nonresonant, pairwise-distinct setting and the local interpretation above.

In particular:

- It credits Proposition 4.7, then uses it to force every sufficiently high z-coefficient of each finite s-jet to vanish exactly. No passage of derivatives through the infinite-index connection limit occurs.
- Parameter-dependent Frobenius solutions and continuation along a fixed path give jointly analytic connection data.
- The s-derivatives are polynomials near z=0 and remain those same polynomials after analytic continuation. At z=1 this rules out the first nonzero singular connection jet, since the singular exponent is fixed and nonintegral.
- Simplicity of the hypergeometric connection zero is checked. The permitted exceptional collision k=0, γ+δ=1 is handled through the symmetric identity 1/(Γ(a)Γ(b))=B/(Γ(1+a)Γ(1+b)); taking analytic individual roots a(B),b(B) there would have been invalid.
- The analytic implicit-function branch and its nonvanishing local factor turn agreement of every finite jet into the convergent expansion required by the conjecture.

No substantive proof gap was found. This audit does not promote the bounded literature search into an absolute priority guarantee.
