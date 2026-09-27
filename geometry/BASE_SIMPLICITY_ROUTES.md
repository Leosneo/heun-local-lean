# Audit of alternatives to the hypergeometric connection formula

The remaining base-simplicity statement concerns the genuine endpoint connection
coefficient (or the equivalent Wronskian) at `s=0, B=−D_k`. Finite recurrence
roots being simple does **not**, by itself, establish this statement.

## Gamma formula route

The written proof uses

`d₂(B,0)=Γ(γ)Γ(δ−1)/(Γ(a)Γ(b))`, with `a+b=γ+δ−1, ab=B`.

This gives a nonzero derivative explicitly; the allowed `k=0, γ+δ=1` case
requires the symmetric reciprocal-gamma calculation. The pinned mathlib does
not contain the required hypergeometric endpoint connection formula.

## Genuine alternative via inhomogeneous polynomial obstruction

If the base connection zero were multiple, differentiating the normalized
solution in B would produce a function regular at both endpoints satisfying

`(L₀−D_k)w=−φ_k`.

There is no polynomial solution: in the polynomial eigenbasis the φ_k component
of the image of L₀−D_k is zero. A possible Gamma-free proof would therefore show
that every solution of this inhomogeneous equation regular at both endpoints
is polynomial. Mathematically, one can seek global single-valued continuation
across the plane and use the regular-singular behavior at infinity to deduce
polynomial growth, then apply Liouville's theorem.

This route does not reduce to the finite polynomial calculation alone. It still
requires substantial global analytic continuation and growth theorems. Neither
was assumed or claimed to have been formalized here.

## Alternative via a weighted adjoint integral

The Lagrange identity with Jacobi weight reduces the derivative of the connection
coefficient to a weighted square norm of φ_k. For positive real γ,δ this integral
is nonzero by positivity. Extending that conclusion to the source's arbitrary
complex nonresonant parameters requires the explicit Jacobi/Beta norm formula
and parameter continuation, or a Pochhammer contour treatment. Positivity only
proves a restricted parameter case; it cannot replace the full source theorem.

## Checked work supplied instead

`lean/ODEUniqueness.lean` proves ordinary-point analytic second-order ODE
uniqueness using vanishing orders. A nonzero solution vanishing together with its
first derivative would have order at least two, and its second derivative has
strictly smaller order than the remaining ODE terms, a contradiction.

The file also proves connected-domain uniqueness, closure under constant linear
combinations, and construction of the actual connection identity from a pair
with nonzero ordinary-point Wronskian. These are independently useful checked
analytic steps, but they do not establish base accessory-parameter simplicity.
