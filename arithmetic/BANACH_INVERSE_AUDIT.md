# Independent bounded inverse audit

Checked on 2026-09-27 using the pinned mathlib environment.

`BanachInverse.lean` constructs the weighted upper shift on bounded complex sequences as an actual continuous linear map. Its operator norm is bounded by the uniform coefficient bound. For a bound below one, the geometric-series theorem gives an actual continuous linear equivalence for identity plus shift. The proof then solves a uniformly invertible diagonal bidiagonal recurrence, extends across a finite prefix by induction, and reindexes to give the unique bounded tail above any specified degree.

`BanachInvertible.lean` instantiates this theorem with the literal normalized Heun diagonal and upper coefficients from `BanachOperators.lean`. Their eventual inverse-diagonal and ratio bounds are proved from their limits, not assumed. The only diagonal zero is at the base polynomial degree k. `BanachHead.lean` determines the accessory correction from that resonant row, then solves the finite head from its prescribed zeroth coefficient. The base polynomial has nonzero coefficient at k and vanishes above k. Consequently the actual bordered continuous linear operator is bijective; the Banach inverse theorem supplies its continuous inverse.

Main checked declaration:

```
Heun.borderT_isInvertible (f : Family) (p : Parameters)
  (hp : Admissible f p) (k : Nat) : (borderT f p k).IsInvertible
```

The operator is exactly

```
(x,b) ↦ (seqA p k x − b • seqJ (seqBase f p k), x 0).
```

Its kernel/range properties are not supplied as hypotheses. Its axioms are only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or new axiom occurs in the checked dependency chain.

Sign audit: after dividing the nth equation by 2^n, the nonlinear equation `seqA x − b • seqJ x + s • seqV x = 0` reads

```
(n+1)(n+γ)c_(n+1) − (D_n−D_k+b)c_n − s E_n c_n + s F_n c_(n−1)=0.
```

Thus the source accessory parameter is exactly B=−D_k+b. The branch uses the full coefficient sequence, whose zeroth coefficient is one, not a correction sequence accidentally given the wrong normalization.

These results supply the central inverse for the implicit eigenpair route. They alone are not the final literature conjecture: the analytic branch, connection-zero interpretation, and stabilized Taylor identification must also be assembled and checked.
