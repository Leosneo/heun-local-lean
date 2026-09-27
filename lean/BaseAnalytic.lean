import BaseEigenfunction
import OperatorBridge

noncomputable section
namespace Heun
open Polynomial GcoyHeun

theorem L0_reflection (gamma delta : ℂ) (q : Poly) :
    L0 delta gamma (q.comp (1 - X)) = (L0 gamma delta q).comp (1 - X) := by
  simp [L0_differential, derivative_comp, derivative_sub,
    mul_comp, add_comp, sub_comp]
  ring

/-- Polynomial solutions of the unperturbed equation are determined by their
constant coefficient, using exactly the nonresonance needed at zero. -/
theorem polynomial_eigenfunction_zero_of_constant_zero
    (gamma delta lambda : ℂ) (q : Poly)
    (hgamma : ∀ n : ℕ, gamma ≠ -(n : ℂ))
    (hq : L0 gamma delta q = C lambda * q) (hzero : q.coeff 0 = 0) : q = 0 := by
  have hc : ∀ n, q.coeff n = 0 := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
      have he := congrArg (fun r : Poly => r.coeff n) hq
      dsimp only at he
      rw [coeff_L0, coeff_C_mul, ih] at he
      have hd := single_denominator_ne_zero gamma hgamma n
      have hm : (((n : ℂ) + 1) * ((n : ℂ) + gamma)) * q.coeff (n+1) = 0 := by
        linear_combination -he
      exact (mul_eq_zero.mp hm).resolve_left hd
  ext n
  simpa using hc n

theorem basePolynomial_eval_one_ne_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) : (basePolynomial f p k).eval 1 ≠ 0 := by
  intro hz
  let q := basePolynomial f p k
  have he := basePolynomial_eigenfunction f p k (admissible_gamma_nonpositive f p hp)
  have hrefl : L0 p.delta p.gamma (q.comp (1-X)) = C (D p k) * q.comp (1-X) := by
    rw [L0_reflection]
    change (L0 p.gamma p.delta (basePolynomial f p k)).comp (1-X) = _
    rw [he]
    simp [mul_comp, q]
  have hc : (q.comp (1-X)).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simpa [q] using hz
  have hq : q.comp (1-X) = 0 := polynomial_eigenfunction_zero_of_constant_zero
    p.delta p.gamma (D p k) (q.comp (1-X))
    (fun n => by simpa using hp.2.1 (-(n : ℤ))) hrefl hc
  have hv := congrArg (fun r : Poly => r.eval 1) hq
  have h0 := basePolynomial_normalized f p k
  rw [coeff_zero_eq_eval_zero] at h0
  simp [eval_comp, q, h0] at hv

theorem basePolynomial_equation (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    equationPolynomial f p (-D p k) 0 (basePolynomial f p k) = 0 := by
  simp [equationPolynomial,
    basePolynomial_eigenfunction f p k (admissible_gamma_nonpositive f p hp)]

/-- The constructed eigenfunction solves the literal complex differential
equation everywhere away from its two fixed singular points. -/
theorem basePolynomial_solves (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    SolvesOn f p (-D p k) 0 (fun z => (basePolynomial f p k).eval z)
      ({0, 1}ᶜ : Set ℂ) := by
  apply polynomial_solvesOn_of_equation
  · intro z hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact hz.1
  · intro z hz
    apply sub_ne_zero.mpr
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact hz.2
  · intro z _
    simp
  · exact basePolynomial_equation f p hp k

/-- Both normalized regular endpoint solutions exist at the unperturbed
eigenvalue, with a nonzero connection multiplier. These are actual analytic
solutions of the source ODE, not abstract vectors. -/
theorem base_regular_endpoint_pair (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    ∃ (y u : ℂ → ℂ) (a : ℂ),
      AnalyticOnNhd ℂ y Set.univ ∧ AnalyticOnNhd ℂ u Set.univ ∧
      y 0 = 1 ∧ u 1 = 1 ∧ a ≠ 0 ∧
      SolvesOn f p (-D p k) 0 y ({0, 1}ᶜ : Set ℂ) ∧
      SolvesOn f p (-D p k) 0 u ({0, 1}ᶜ : Set ℂ) ∧
      ∀ z, y z = a * u z := by
  let q := basePolynomial f p k
  let a := q.eval 1
  have ha : a ≠ 0 := basePolynomial_eval_one_ne_zero f p hp k
  let v : Poly := C a⁻¹ * q
  refine ⟨fun z => q.eval z, fun z => v.eval z, a,
    AnalyticOnNhd.eval_polynomial q, AnalyticOnNhd.eval_polynomial v, ?_, ?_, ha,
    basePolynomial_solves f p hp k, ?_, ?_⟩
  · exact (coeff_zero_eq_eval_zero q).symm.trans (basePolynomial_normalized f p k)
  · simp [v, a, ha]
  · apply polynomial_solvesOn_of_equation
    · intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
      exact hz.1
    · intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
      exact sub_ne_zero.mpr hz.2
    · intro z _
      simp
    · rw [show v = C a⁻¹ * q from rfl, equationPolynomial_C_mul]
      simp [q, basePolynomial_equation f p hp k]
  · intro z
    simp [v, ha]

end Heun
#print axioms Heun.basePolynomial_solves
#print axioms Heun.basePolynomial_eval_one_ne_zero
#print axioms Heun.base_regular_endpoint_pair
