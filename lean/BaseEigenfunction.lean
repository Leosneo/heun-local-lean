import HeunProblem
import PolynomialGrammar
import FiniteRoot

/-!
An actual normalized polynomial eigenfunction of the unperturbed Heun operator.
The witness is constructed from the source recurrence; existence is not assumed.
This is an algebraic theorem, not a formalization of the analytic conjecture.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace Heun

def basePolynomial (f : Family) (p : Parameters) (k : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (k + 1), monomial n (coefficient f p (-D p k) 0 n)

theorem coeff_basePolynomial (f : Family) (p : Parameters) (k n : ℕ) :
    (basePolynomial f p k).coeff n = coefficient f p (-D p k) 0 n := by
  classical
  by_cases hn : n < k + 1
  · simp [basePolynomial, finset_sum_coeff, coeff_monomial, Finset.mem_range, hn]
  · have hkn : k < n := by omega
    rw [coefficient_base_root f p hkn]
    simp [basePolynomial, finset_sum_coeff, coeff_monomial, Finset.mem_range, hn]

theorem basePolynomial_normalized (f : Family) (p : Parameters) (k : ℕ) :
    (basePolynomial f p k).coeff 0 = 1 := by
  rw [coeff_basePolynomial, coefficient_zero]

theorem basePolynomial_bounded (f : Family) (p : Parameters) (k : ℕ) :
    GcoyHeun.Bounded k (basePolynomial f p k) := by
  intro n hn
  rw [coeff_basePolynomial, coefficient_base_root f p hn]

theorem admissible_gamma_nonpositive (f : Family) (p : Parameters)
    (hp : Admissible f p) (n : ℕ) : p.gamma ≠ -(n : ℂ) := by
  simpa using hp.1 (-(n : ℤ))

theorem single_denominator_ne_zero (gamma : ℂ)
    (hgamma : ∀ n : ℕ, gamma ≠ -(n : ℂ)) (n : ℕ) :
    ((n : ℂ) + 1) * ((n : ℂ) + gamma) ≠ 0 := by
  apply mul_ne_zero
  · have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simpa using h
  · intro h
    apply hgamma n
    linear_combination h

/-- Clear the genuine recurrence denominator at zero perturbation. -/
theorem coefficient_zero_parameter_cleared (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B : ℂ) (n : ℕ) :
    (((n : ℂ) + 1) * ((n : ℂ) + p.gamma)) * coefficient f p B 0 (n + 1) =
      (B + D p n) * coefficient f p B 0 n := by
  change (((n : ℂ) + 1) * ((n : ℂ) + p.gamma)) *
    (((B + D p n + 0 * E f p n) * (coefficientPair f p B 0 n).2 -
      0 * F f p n * (coefficientPair f p B 0 n).1) /
        (((n : ℂ) + 1) * ((n : ℂ) + p.gamma))) = _
  simp only [zero_mul, add_zero, sub_zero]
  rw [mul_div_cancel₀ _ (single_denominator_ne_zero p.gamma hgamma n)]
  rfl

theorem basePolynomial_eigenfunction (f : Family) (p : Parameters) (k : ℕ)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) :
    GcoyHeun.L0 p.gamma p.delta (basePolynomial f p k) =
      C (D p k) * basePolynomial f p k := by
  ext n
  rw [GcoyHeun.coeff_L0, coeff_C_mul]
  simp only [coeff_basePolynomial]
  have h := coefficient_zero_parameter_cleared f p hgamma (-D p k) n
  change D p n * coefficient f p (-D p k) 0 n -
    ((n : ℂ) + 1) * ((n : ℂ) + p.gamma) * coefficient f p (-D p k) 0 (n+1) = _
  rw [h]
  ring

/-- Constructive existence under the actual literature admissibility assumptions. -/
theorem exists_normalized_base_eigenfunction (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    ∃ q : Polynomial ℂ, q.coeff 0 = 1 ∧ GcoyHeun.Bounded k q ∧
      GcoyHeun.L0 p.gamma p.delta q = C (D p k) * q := by
  exact ⟨basePolynomial f p k, basePolynomial_normalized f p k,
    basePolynomial_bounded f p k,
    basePolynomial_eigenfunction f p k (admissible_gamma_nonpositive f p hp)⟩

theorem basePolynomial_top_ne_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) : (basePolynomial f p k).coeff k ≠ 0 := by
  rw [coeff_basePolynomial, coefficient_at_s_zero]
  apply div_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro m hm hz
    have hD : D p m = D p k := by linear_combination hz
    have hinj : Function.Injective (D p) := by
      have hfun : D p = (fun n : ℕ => (n : ℂ) * ((n : ℂ) - 1 + (p.gamma + p.delta))) := by
        funext n
        simp only [D]
        ring
      rw [hfun]
      exact MoriTakemura.quadratic_diagonal_injective (p.gamma + p.delta) hp.2.2.1
    have hmk := hinj hD
    have hm' := Finset.mem_range.mp hm
    omega
  · exact MoriTakemura.recurrence_denominator_ne_zero p.gamma
      (admissible_gamma_nonpositive f p hp) k

theorem basePolynomial_natDegree (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) : (basePolynomial f p k).natDegree = k := by
  apply le_antisymm
  · exact natDegree_le_iff_coeff_eq_zero.mpr (basePolynomial_bounded f p k)
  · exact le_natDegree_of_ne_zero (basePolynomial_top_ne_zero f p hp k)

/-- The constructed normalized eigenfunction has exactly the expected degree. -/
theorem exists_normalized_base_eigenfunction_exact_degree (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    ∃ q : Polynomial ℂ, q.coeff 0 = 1 ∧ q.natDegree = k ∧
      GcoyHeun.L0 p.gamma p.delta q = C (D p k) * q := by
  exact ⟨basePolynomial f p k, basePolynomial_normalized f p k,
    basePolynomial_natDegree f p hp k,
    basePolynomial_eigenfunction f p k (admissible_gamma_nonpositive f p hp)⟩

#print axioms exists_normalized_base_eigenfunction
#print axioms exists_normalized_base_eigenfunction_exact_degree

end Heun
