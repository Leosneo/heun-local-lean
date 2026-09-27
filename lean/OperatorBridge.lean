import HeunProblem
import PolynomialGrammar
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Analytic.Polynomial

/-! The polynomial operators are identified with the actual complex ODE.
This bridge checks all three families, including their rational denominators.
-/
noncomputable section
namespace Heun
open Polynomial GcoyHeun

def perturbation (f : Family) (p : Parameters) (q : Poly) : Poly :=
  match f with
  | .heun => VHeun p.gamma p.delta p.epsilon p.alpha p.beta q
  | .confluent => VConfluent p.alpha q
  | .reduced => VReduced q

def equationPolynomial (f : Family) (p : Parameters) (B s : ℂ) (q : Poly) : Poly :=
  L0 p.gamma p.delta q + C s * perturbation f p q + C B * q

def clearedDenominator (f : Family) (s z : ℂ) : ℂ :=
  z * (z - 1) * (match f with | .heun => 1 - s * z | _ => 1)

theorem polynomial_second_deriv (q : Poly) (z : ℂ) :
    deriv (deriv (fun w : ℂ => q.eval w)) z = q.derivative.derivative.eval z := by
  have h : deriv (fun w : ℂ => q.eval w) = fun w => q.derivative.eval w := by
    funext w
    exact q.deriv
  rw [h]
  exact q.derivative.deriv

theorem equationPolynomial_eval (f : Family) (p : Parameters) (B s z : ℂ)
    (q : Poly) (hz : z ≠ 0) (hz1 : z - 1 ≠ 0)
    (hsm : 1 - s * z ≠ 0) :
    (equationPolynomial f p B s q).eval z =
      clearedDenominator f s z *
        (deriv (deriv (fun w : ℂ => q.eval w)) z +
          drift f p s z * deriv (fun w : ℂ => q.eval w) z +
          potential f p B s z * q.eval z) := by
  rw [polynomial_second_deriv, q.deriv]
  have hsm' : 1 - z * s ≠ 0 := by simpa [mul_comm] using hsm
  cases f <;>
    simp [equationPolynomial, perturbation, L0_differential,
      VHeun_differential, VConfluent_differential, VReduced,
      clearedDenominator, drift, potential] <;>
    field_simp [hz, hz1, hsm, hsm'] <;> ring

theorem polynomial_solvesOn_of_equation (f : Family) (p : Parameters)
    (B s : ℂ) (q : Poly) (U : Set ℂ)
    (hz : ∀ z ∈ U, z ≠ 0) (hz1 : ∀ z ∈ U, z - 1 ≠ 0)
    (hsm : ∀ z ∈ U, 1 - s * z ≠ 0)
    (hq : equationPolynomial f p B s q = 0) :
    SolvesOn f p B s (fun z => q.eval z) U := by
  constructor
  · intro z _
    exact AnalyticOnNhd.eval_polynomial q z (Set.mem_univ z)
  · intro z hzU
    have he := equationPolynomial_eval f p B s z q
      (hz z hzU) (hz1 z hzU) (hsm z hzU)
    rw [hq, eval_zero] at he
    have hd : clearedDenominator f s z ≠ 0 := by
      cases f <;> simp [clearedDenominator, hz z hzU, hz1 z hzU, hsm z hzU]
    exact (mul_eq_zero.mp he.symm).resolve_left hd

theorem equationPolynomial_coeff_zero (f : Family) (p : Parameters)
    (B s : ℂ) (q : Poly) :
    (equationPolynomial f p B s q).coeff 0 =
      B * q.coeff 0 - p.gamma * q.coeff 1 := by
  cases f <;> simp [equationPolynomial, perturbation, coeff_L0,
    coeff_VHeun_zero, coeff_VConfluent_zero, coeff_VReduced_zero] <;> ring

theorem equationPolynomial_coeff_succ (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (q : Poly) (n : ℕ) :
    (equationPolynomial f p B s q).coeff (n + 1) =
      (B + D p (n + 1) + s * E f p (n + 1)) * q.coeff (n + 1) -
      s * F f p (n + 1) * q.coeff n -
      (((n : ℂ) + 2) * ((n : ℂ) + 1 + p.gamma)) * q.coeff (n + 2) := by
  cases f with
  | heun =>
    have hb := hp.2.2.2 rfl
    simp [equationPolynomial, perturbation, coeff_L0,
      coeff_VHeun_succ _ _ _ _ _ _ _ hb, D, E, F]
    ring
  | confluent =>
    simp [equationPolynomial, perturbation, coeff_L0, coeff_VConfluent_succ, D, E, F]
    ring
  | reduced =>
    simp [equationPolynomial, perturbation, coeff_L0, coeff_VReduced_succ, D, E, F]
    ring

/-- A normalized polynomial satisfying the differential equation has exactly
the coefficients defined by the source recurrence, at every index. -/
theorem polynomial_coefficients_eq_recurrence (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (q : Poly)
    (hq : equationPolynomial f p B s q = 0) (h0 : q.coeff 0 = 1) :
    ∀ n, q.coeff n = coefficient f p B s n := by
  have hg : p.gamma ≠ 0 := by simpa using hp.1 0
  have h1 : q.coeff 1 = coefficient f p B s 1 := by
    rw [coefficient_one]
    apply (eq_div_iff hg).mpr
    have he := congrArg (fun r : Poly => r.coeff 0) hq
    dsimp only at he
    rw [equationPolynomial_coeff_zero, h0] at he
    simp only [coeff_zero, mul_one] at he
    linear_combination -he
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => exact h1
  | more n ih0 ih1 =>
    rw [coefficient_recurrence]
    apply (eq_div_iff (recurrence_denominator_ne_zero hp (n+1))).mpr
    have he := congrArg (fun r : Poly => r.coeff (n+1)) hq
    dsimp only at he
    rw [equationPolynomial_coeff_succ f p hp, ih0, ih1] at he
    simp only [coeff_zero, Nat.cast_add, Nat.cast_one] at he ⊢
    linear_combination -he

theorem equationPolynomial_C_mul (f : Family) (p : Parameters)
    (B s a : ℂ) (q : Poly) :
    equationPolynomial f p B s (C a * q) = C a * equationPolynomial f p B s q := by
  cases f <;>
    simp [equationPolynomial, perturbation, L0, theta, VHeun, VConfluent, VReduced,
      derivative_mul] <;> ring

end Heun
#print axioms Heun.polynomial_solvesOn_of_equation
#print axioms Heun.polynomial_coefficients_eq_recurrence
