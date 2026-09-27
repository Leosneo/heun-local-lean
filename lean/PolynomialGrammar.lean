import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
Concrete polynomial grammar for the Heun perturbation argument.
This file proves algebraic finite-degree propagation only. It does not assert
analytic dependence, connection formulae, or the literature conjecture.
-/

namespace GcoyHeun
open Polynomial
noncomputable section

abbrev Poly := Polynomial ℂ

/-- Exact coefficient formulation of the polynomial filtration. -/
def Bounded (d : ℕ) (p : Poly) : Prop := ∀ n, d < n → p.coeff n = 0

def theta (p : Poly) : Poly := X * p.derivative

theorem coeff_theta (p : Poly) (n : ℕ) :
    (theta p).coeff n = (n : ℂ) * p.coeff n := by
  cases n with
  | zero => simp [theta]
  | succ n => simp [theta, coeff_X_mul, coeff_derivative, mul_comm]

theorem bounded_add {d : ℕ} {p q : Poly} (hp : Bounded d p) (hq : Bounded d q) :
    Bounded d (p + q) := by
  intro n hn
  simp [hp n hn, hq n hn]

theorem bounded_sub {d : ℕ} {p q : Poly} (hp : Bounded d p) (hq : Bounded d q) :
    Bounded d (p - q) := by
  intro n hn
  simp [hp n hn, hq n hn]

theorem bounded_neg {d : ℕ} {p : Poly} (hp : Bounded d p) : Bounded d (-p) := by
  intro n hn
  simp [hp n hn]

theorem bounded_const_mul {d : ℕ} {p : Poly} (a : ℂ) (hp : Bounded d p) :
    Bounded d (C a * p) := by
  intro n hn
  simp [coeff_C_mul, hp n hn]

theorem bounded_mono {d e : ℕ} {p : Poly} (h : d ≤ e) (hp : Bounded d p) :
    Bounded e p := by
  intro n hn
  exact hp n (lt_of_le_of_lt h hn)

theorem bounded_derivative {d : ℕ} {p : Poly} (hp : Bounded d p) :
    Bounded d p.derivative := by
  intro n hn
  rw [coeff_derivative, hp (n + 1) (by omega), zero_mul]

theorem bounded_theta {d : ℕ} {p : Poly} (hp : Bounded d p) :
    Bounded d (theta p) := by
  intro n hn
  rw [coeff_theta, hp n hn, mul_zero]

theorem bounded_X_mul {d : ℕ} {p : Poly} (hp : Bounded d p) :
    Bounded (d + 1) (X * p) := by
  intro n hn
  cases n with
  | zero => omega
  | succ n => rw [coeff_X_mul]; exact hp n (by omega)

/-- The unperturbed hypergeometric differential operator. -/
def L0 (gamma delta : ℂ) (p : Poly) : Poly :=
  theta (theta p) + C (gamma + delta - 1) * theta p -
    theta p.derivative - C gamma * p.derivative

theorem L0_differential (gamma delta : ℂ) (p : Poly) :
    L0 gamma delta p = X * (X - 1) * p.derivative.derivative +
      (C (gamma + delta) * X - C gamma) * p.derivative := by
  simp [L0, theta, derivative_mul, derivative_X, map_add, map_sub]
  ring

theorem bounded_L0 {d : ℕ} {p : Poly} (gamma delta : ℂ) (hp : Bounded d p) :
    Bounded d (L0 gamma delta p) := by
  exact bounded_sub (bounded_sub
    (bounded_add (bounded_theta (bounded_theta hp))
      (bounded_const_mul _ (bounded_theta hp)))
    (bounded_theta (bounded_derivative hp)))
    (bounded_const_mul _ (bounded_derivative hp))

/-- The exact lower-bidiagonal coefficient action of the unperturbed operator. -/
theorem coeff_L0 (gamma delta : ℂ) (p : Poly) (n : ℕ) :
    (L0 gamma delta p).coeff n =
      (n : ℂ) * ((n : ℂ) - 1 + gamma + delta) * p.coeff n -
      ((n : ℂ) + 1) * ((n : ℂ) + gamma) * p.coeff (n + 1) := by
  simp only [L0, coeff_sub, coeff_add, coeff_theta, coeff_C_mul, coeff_derivative]
  ring

/-- On a filtration quotient the eigenvalue is D_n=n(n-1+gamma+delta). -/
theorem coeff_L0_top {n : ℕ} {p : Poly} (gamma delta : ℂ) (hp : Bounded n p) :
    (L0 gamma delta p).coeff n =
      (n : ℂ) * ((n : ℂ) - 1 + gamma + delta) * p.coeff n := by
  rw [coeff_L0, hp (n + 1) (by omega)]
  ring

/-- The three perturbations in their Euler-operator presentations. -/
def VHeun (gamma delta eps alpha beta : ℂ) (p : Poly) : Poly :=
  -(X * theta (theta p)) - C (gamma + delta + eps - 1) * (X * theta p) -
    C (alpha * beta) * (X * p) + theta (theta p) +
    C (gamma + eps - 1) * theta p

def VConfluent (alpha : ℂ) (p : Poly) : Poly :=
  -(X * theta p) + theta p - C alpha * (X * p)

def VReduced (p : Poly) : Poly := -(X * p)

theorem VHeun_differential (gamma delta eps alpha beta : ℂ) (p : Poly) :
    VHeun gamma delta eps alpha beta p =
      -(X ^ 2 * (X - 1) * p.derivative.derivative) -
      (C gamma * X * (X - 1) + C delta * X ^ 2 + C eps * X * (X - 1)) *
        p.derivative - C (alpha * beta) * X * p := by
  simp [VHeun, theta, derivative_mul, derivative_X, map_add, map_sub]
  ring

theorem VConfluent_differential (alpha : ℂ) (p : Poly) :
    VConfluent alpha p = -(X * (X - 1) * p.derivative) - C alpha * X * p := by
  simp only [VConfluent, theta]
  ring

theorem coeff_VHeun_succ (gamma delta eps alpha beta : ℂ) (p : Poly) (n : ℕ)
    (hbalance : gamma + delta + eps = alpha + beta + 1) :
    (VHeun gamma delta eps alpha beta p).coeff (n + 1) =
      ((n : ℂ) + 1) * ((n : ℂ) + gamma + eps) * p.coeff (n + 1) -
      ((n : ℂ) + alpha) * ((n : ℂ) + beta) * p.coeff n := by
  simp only [VHeun, coeff_add, coeff_sub, coeff_neg, coeff_C_mul,
    coeff_X_mul, coeff_theta, hbalance, Nat.cast_add, Nat.cast_one]
  ring

theorem coeff_VConfluent_succ (alpha : ℂ) (p : Poly) (n : ℕ) :
    (VConfluent alpha p).coeff (n + 1) =
      ((n : ℂ) + 1) * p.coeff (n + 1) - ((n : ℂ) + alpha) * p.coeff n := by
  simp only [VConfluent, coeff_add, coeff_sub, coeff_neg, coeff_C_mul,
    coeff_X_mul, coeff_theta, Nat.cast_add, Nat.cast_one]
  ring

theorem coeff_VReduced_succ (p : Poly) (n : ℕ) :
    (VReduced p).coeff (n + 1) = -p.coeff n := by
  simp [VReduced, coeff_X_mul]

theorem coeff_VHeun_zero (gamma delta eps alpha beta : ℂ) (p : Poly) :
    (VHeun gamma delta eps alpha beta p).coeff 0 = 0 := by
  simp [VHeun, coeff_theta]

theorem coeff_VConfluent_zero (alpha : ℂ) (p : Poly) :
    (VConfluent alpha p).coeff 0 = 0 := by
  simp [VConfluent, coeff_theta]

theorem coeff_VReduced_zero (p : Poly) : (VReduced p).coeff 0 = 0 := by
  simp [VReduced]

theorem bounded_VHeun {d : ℕ} {p : Poly}
    (gamma delta eps alpha beta : ℂ) (hp : Bounded d p) :
    Bounded (d + 1) (VHeun gamma delta eps alpha beta p) := by
  exact bounded_add (bounded_add (bounded_sub (bounded_sub
    (bounded_neg (bounded_X_mul (bounded_theta (bounded_theta hp))))
    (bounded_const_mul _ (bounded_X_mul (bounded_theta hp))))
    (bounded_const_mul _ (bounded_X_mul hp)))
    (bounded_mono (by omega) (bounded_theta (bounded_theta hp))))
    (bounded_const_mul _ (bounded_mono (by omega) (bounded_theta hp)))

theorem bounded_VConfluent {d : ℕ} {p : Poly} (alpha : ℂ) (hp : Bounded d p) :
    Bounded (d + 1) (VConfluent alpha p) := by
  exact bounded_sub (bounded_add (bounded_neg (bounded_X_mul (bounded_theta hp)))
    (bounded_mono (by omega) (bounded_theta hp))) (bounded_const_mul _ (bounded_X_mul hp))

theorem bounded_VReduced {d : ℕ} {p : Poly} (hp : Bounded d p) :
    Bounded (d + 1) (VReduced p) := bounded_neg (bounded_X_mul hp)

/-- Any word of j degree-raising grammar operations reaches at most degree k+j. -/
theorem bounded_iterate (V : Poly → Poly)
    (hV : ∀ d p, Bounded d p → Bounded (d + 1) (V p))
    {k : ℕ} {p : Poly} (hp : Bounded k p) (j : ℕ) :
    Bounded (k + j) ((V^[j]) p) := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
      simpa [Function.iterate_succ_apply', Nat.add_assoc] using hV (k+j) ((V^[j]) p) ih

end
end GcoyHeun
