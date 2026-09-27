import BaseAnalytic
import FrobeniusOne
import SingularSolution

/-! Identification of the literal endpoint series at an unperturbed eigenvalue. -/
noncomputable section
open Polynomial GcoyHeun
namespace Heun

theorem frobeniusSum_basePolynomial (f : Family) (p : Parameters) (k : ℕ) (z : ℂ) :
    frobeniusSum f p (-D p k) 0 z = (basePolynomial f p k).eval z := by
  rw [frobeniusSum, tsum_eq_sum (s := Finset.range (k+1))]
  · simp [basePolynomial, eval_finset_sum, eval_monomial]
  · intro n hn
    have hkn : k < n := by
      have h : ¬n < k+1 := by simpa using hn
      omega
    rw [coefficient_base_root f p hkn, zero_mul]

theorem reflected_D (p : Parameters) (k : ℕ) : D (reflectedParameters p) k = D p k := by
  simp only [D, reflectedParameters]
  ring

theorem reflected_admissible (f : Family) (p : Parameters) (hp : Admissible f p) :
    Admissible f (reflectedParameters p) := by
  refine ⟨hp.2.1, hp.1, ?_, ?_⟩
  · intro m
    simpa [reflectedParameters, add_comm] using hp.2.2.1 m
  · intro hf
    dsimp [reflectedParameters]
    linear_combination hp.2.2.2 hf

theorem reflected_basePolynomial (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    basePolynomial f (reflectedParameters p) k =
      C ((basePolynomial f p k).eval 1)⁻¹ * (basePolynomial f p k).comp (1-X) := by
  let q := basePolynomial f p k
  let a := q.eval 1
  have ha : a ≠ 0 := basePolynomial_eval_one_ne_zero f p hp k
  have hqr : equationPolynomial f (reflectedParameters p) (-D p k) 0 (q.comp (1-X)) = 0 := by
    simp only [equationPolynomial, zero_mul, map_zero, add_zero]
    change L0 p.delta p.gamma (q.comp (1-X)) + C (-D p k) * q.comp (1-X) = 0
    rw [L0_reflection]
    dsimp [q]
    rw [basePolynomial_eigenfunction f p k (admissible_gamma_nonpositive f p hp)]
    simp [mul_comp]
  have hscaled : equationPolynomial f (reflectedParameters p) (-D p k) 0
      (C a⁻¹ * q.comp (1-X)) = 0 := by
    rw [equationPolynomial_C_mul, hqr, mul_zero]
  have hzero : (C a⁻¹ * q.comp (1-X)).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]
    simp [a, ha, eval_comp]
  have hcoeff := polynomial_coefficients_eq_recurrence f (reflectedParameters p)
    (reflected_admissible f p hp) (-D p k) 0 (C a⁻¹ * q.comp (1-X)) hscaled hzero
  ext n
  rw [coeff_basePolynomial, reflected_D]
  exact (hcoeff n).symm

theorem regularOne_basePolynomial (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (z : ℂ) :
    regularOne f p (-D p k) 0 z =
      ((basePolynomial f p k).eval 1)⁻¹ * (basePolynomial f p k).eval z := by
  have hs : reflectedParameter f 0 = 0 := by cases f <;> simp [reflectedParameter]
  have hB : reflectedAccessory f p (-D p k) 0 = -D p k := by
    cases f <;> simp [reflectedAccessory]
  rw [regularOne, hs, hB, ← reflected_D p k, frobeniusSum_basePolynomial,
    reflected_basePolynomial f p hp k]
  simp [eval_comp]

theorem base_actual_regular_connection (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (z : ℂ) :
    frobeniusSum f p (-D p k) 0 z =
      (basePolynomial f p k).eval 1 * regularOne f p (-D p k) 0 z := by
  rw [frobeniusSum_basePolynomial, regularOne_basePolynomial f p hp]
  have ha := basePolynomial_eval_one_ne_zero f p hp k
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

/-- Assembly lemma: the supplied singular factor is an actual analytic ODE
solution, not a connection coefficient defined from the target series. -/
theorem base_connection_of_singular_factor (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (h : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ h oneDisk) (h1 : h 1 = 1)
    (hsol : SolvesOn f p (-D p k) 0 (singularSolution p h) overlap) :
    IsConnectionCoefficient f p (-D p k) 0 0 := by
  obtain ⟨hya, hy0, hys⟩ := frobeniusSum_regular_zero_solution f p hp (-D p k) 0
    (by norm_num)
  have hd : ∀ n : ℕ, p.delta ≠ -(n:ℂ) := by
    intro n
    simpa using hp.2.1 (-(n:ℤ))
  obtain ⟨hua, hu1, hus⟩ := regularOne_solution f p hd hp.2.2.2 (-D p k) 0
    (by norm_num)
  refine ⟨frobeniusSum f p (-D p k) 0, regularOne f p (-D p k) 0, h,
    (basePolynomial f p k).eval 1, hya, hy0, hys, hua, hu1, hus, ha, h1, hsol, ?_⟩
  intro z _
  simpa using base_actual_regular_connection f p hp k z

/-- The literal connection coefficient is zero at each unperturbed eigenvalue.
All three endpoint solutions in its definition are explicitly constructed. -/
theorem base_IsConnectionCoefficient (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    IsConnectionCoefficient f p (-D p k) 0 0 := by
  obtain ⟨ha, h1, hsol⟩ := singularFactor_solution f p hp.2.1 hp.2.2.2
    (-D p k) 0 (by norm_num)
  exact base_connection_of_singular_factor f p hp k
    (singularFactor f p (-D p k) 0) ha h1 hsol

#print axioms frobeniusSum_basePolynomial
#print axioms regularOne_basePolynomial
#print axioms base_actual_regular_connection
#print axioms base_IsConnectionCoefficient
end Heun
