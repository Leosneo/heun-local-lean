import BaseEigenfunction
import Mathlib.Algebra.Polynomial.Sequence

/-! Algebraic eigenbasis and inversion tools for perturbation jets.
No analytic existence assertion is made in this file. -/
noncomputable section
open Polynomial Module

namespace Heun

def baseSequence (f : Family) (p : Parameters) (hp : Admissible f p) :
    Polynomial.Sequence ℂ where
  elems' := basePolynomial f p
  degree_eq' k := by
    have hne : basePolynomial f p k ≠ 0 := by
      intro hz
      have h := basePolynomial_normalized f p k
      rw [hz] at h
      simp at h
    rw [Polynomial.degree_eq_natDegree hne, basePolynomial_natDegree f p hp k]

theorem baseSequence_unit (f : Family) (p : Parameters) (hp : Admissible f p) (k : ℕ) :
    IsUnit ((baseSequence f p hp) k).leadingCoeff := by
  apply isUnit_iff_ne_zero.mpr
  exact leadingCoeff_ne_zero.mpr ((baseSequence f p hp).ne_zero k)

def baseBasis (f : Family) (p : Parameters) (hp : Admissible f p) :
    Basis ℕ ℂ (Polynomial ℂ) :=
  (baseSequence f p hp).basis (baseSequence_unit f p hp)

theorem baseBasis_apply (f : Family) (p : Parameters) (hp : Admissible f p) (k : ℕ) :
    baseBasis f p hp k = basePolynomial f p k := by
  simp [baseBasis, baseSequence]

def baseOperator (p : Parameters) : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun := GcoyHeun.L0 p.gamma p.delta
  map_add' a b := by
    ext n
    simp only [GcoyHeun.coeff_L0, coeff_add]
    ring
  map_smul' c a := by
    ext n
    simp only [GcoyHeun.coeff_L0, coeff_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem baseOperator_basis (f : Family) (p : Parameters) (hp : Admissible f p) (k : ℕ) :
    baseOperator p (baseBasis f p hp k) = D p k • baseBasis f p hp k := by
  rw [baseBasis_apply]
  change GcoyHeun.L0 p.gamma p.delta (basePolynomial f p k) = _
  rw [basePolynomial_eigenfunction f p k (admissible_gamma_nonpositive f p hp)]
  exact (smul_eq_C_mul _).symm

def reducedInverse (f : Family) (p : Parameters) (hp : Admissible f p) (k : ℕ) :
    Polynomial ℂ →ₗ[ℂ] Polynomial ℂ :=
  (baseBasis f p hp).constr ℂ (fun i =>
    if i = k then 0 else (D p i - D p k)⁻¹ • baseBasis f p hp i)

theorem diagonal_injective (f : Family) (p : Parameters) (hp : Admissible f p) :
    Function.Injective (D p) := by
  have hfun : D p = (fun n : ℕ => (n : ℂ) * ((n : ℂ) - 1 + (p.gamma + p.delta))) := by
    funext n
    simp only [D]
    ring
  rw [hfun]
  exact MoriTakemura.quadratic_diagonal_injective (p.gamma + p.delta) hp.2.2.1

theorem reducedInverse_identity (f : Family) (p : Parameters) (hp : Admissible f p) (k : ℕ) :
    (baseOperator p - D p k • LinearMap.id).comp (reducedInverse f p hp k) +
      ((baseBasis f p hp).coord k).smulRight (baseBasis f p hp k) = LinearMap.id := by
  apply (baseBasis f p hp).ext
  intro i
  by_cases hi : i = k
  · subst i
    simp [reducedInverse]
  · have hD : D p i - D p k ≠ 0 := sub_ne_zero.mpr
      (fun h => hi (diagonal_injective f p hp h))
    simp only [LinearMap.add_apply, LinearMap.comp_apply, reducedInverse,
      Basis.constr_basis, if_neg hi, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul, baseOperator_basis, LinearMap.smulRight_apply]
    have hc : (baseBasis f p hp).coord k (baseBasis f p hp i) = 0 := by
      simp [Basis.coord_apply, hi]
    rw [hc, zero_smul, add_zero, ← sub_smul, smul_smul, inv_mul_cancel₀ hD, one_smul]

/-- Every polynomial has an inhomogeneous preimage modulo the selected eigenspace. -/
theorem exists_inhomogeneous_base_solution (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (rhs : Polynomial ℂ) :
    ∃ (q : Polynomial ℂ) (lambda : ℂ),
      GcoyHeun.L0 p.gamma p.delta q - C (D p k) * q +
        C lambda * basePolynomial f p k = rhs := by
  refine ⟨reducedInverse f p hp k rhs, (baseBasis f p hp).coord k rhs, ?_⟩
  have h := LinearMap.congr_fun (reducedInverse_identity f p hp k) rhs
  simpa [baseOperator, LinearMap.smulRight_apply, smul_eq_C_mul, baseBasis_apply] using h

/-- The free homogeneous component makes the inhomogeneous solution vanish at zero. -/
theorem exists_normalized_inhomogeneous_base_solution (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (rhs : Polynomial ℂ) :
    ∃ (q : Polynomial ℂ) (lambda : ℂ), q.coeff 0 = 0 ∧
      GcoyHeun.L0 p.gamma p.delta q - C (D p k) * q +
        C lambda * basePolynomial f p k = rhs := by
  obtain ⟨q, lambda, hq⟩ := exists_inhomogeneous_base_solution f p hp k rhs
  refine ⟨q - C (q.coeff 0) * basePolynomial f p k, lambda, ?_, ?_⟩
  · simp [basePolynomial_normalized]
  · ext n
    have hqn := congrArg (fun a : Polynomial ℂ => a.coeff n) hq
    have hen := congrArg (fun a : Polynomial ℂ => a.coeff n)
      (basePolynomial_eigenfunction f p k (admissible_gamma_nonpositive f p hp))
    simp only [coeff_sub, coeff_add, coeff_C_mul, GcoyHeun.coeff_L0] at hqn hen ⊢
    linear_combination hqn - q.coeff 0 * hen

theorem inhomogeneous_degree_bound (f : Family) (p : Parameters)
    (hp : Admissible f p) (k d : ℕ) (hkd : k ≤ d)
    (q rhs : Polynomial ℂ) (lambda : ℂ) (hrhs : GcoyHeun.Bounded d rhs)
    (heq : GcoyHeun.L0 p.gamma p.delta q - C (D p k) * q +
      C lambda * basePolynomial f p k = rhs) : GcoyHeun.Bounded d q := by
  apply natDegree_le_iff_coeff_eq_zero.mp
  by_contra hn
  have hdn : d < q.natDegree := by omega
  have hkn : k < q.natDegree := by omega
  have hqne : q ≠ 0 := by
    intro hz
    simp [hz] at hdn
  have hc : q.coeff q.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hqne
  have htop := congrArg (fun a : Polynomial ℂ => a.coeff q.natDegree) heq
  dsimp only at htop
  rw [coeff_add, coeff_sub, GcoyHeun.coeff_L0_top p.gamma p.delta
    (natDegree_le_iff_coeff_eq_zero.mp (le_refl q.natDegree)), coeff_C_mul, coeff_C_mul,
    basePolynomial_bounded f p k q.natDegree hkn, hrhs q.natDegree hdn] at htop
  have hz : (D p q.natDegree - D p k) * q.coeff q.natDegree = 0 := by
    simpa [D, sub_mul] using htop
  have hD := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hc)
  have he := diagonal_injective f p hp hD
  omega

theorem exists_bounded_normalized_inhomogeneous_solution (f : Family) (p : Parameters)
    (hp : Admissible f p) (k d : ℕ) (hkd : k ≤ d)
    (rhs : Polynomial ℂ) (hrhs : GcoyHeun.Bounded d rhs) :
    ∃ (q : Polynomial ℂ) (lambda : ℂ), q.coeff 0 = 0 ∧ GcoyHeun.Bounded d q ∧
      GcoyHeun.L0 p.gamma p.delta q - C (D p k) * q +
        C lambda * basePolynomial f p k = rhs := by
  obtain ⟨q, lambda, hzero, heq⟩ := exists_normalized_inhomogeneous_base_solution f p hp k rhs
  exact ⟨q, lambda, hzero, inhomogeneous_degree_bound f p hp k d hkd q rhs lambda hrhs heq, heq⟩

#print axioms exists_bounded_normalized_inhomogeneous_solution

def perturbationOperator (f : Family) (p : Parameters) : Polynomial ℂ → Polynomial ℂ :=
  match f with
  | .heun => GcoyHeun.VHeun p.gamma p.delta p.epsilon p.alpha p.beta
  | .confluent => GcoyHeun.VConfluent p.alpha
  | .reduced => GcoyHeun.VReduced

theorem perturbationOperator_bounded (f : Family) (p : Parameters)
    {d : ℕ} {q : Polynomial ℂ} (hq : GcoyHeun.Bounded d q) :
    GcoyHeun.Bounded (d+1) (perturbationOperator f p q) := by
  cases f
  · exact GcoyHeun.bounded_VHeun _ _ _ _ _ hq
  · exact GcoyHeun.bounded_VConfluent _ hq
  · exact GcoyHeun.bounded_VReduced hq

def solvePair (f : Family) (p : Parameters) (hp : Admissible f p)
    (k : ℕ) (rhs : Polynomial ℂ) : Polynomial ℂ × ℂ :=
  let h := exists_normalized_inhomogeneous_base_solution f p hp k rhs
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

theorem solvePair_spec (f : Family) (p : Parameters) (hp : Admissible f p)
    (k : ℕ) (rhs : Polynomial ℂ) :
    (solvePair f p hp k rhs).1.coeff 0 = 0 ∧
      GcoyHeun.L0 p.gamma p.delta (solvePair f p hp k rhs).1 -
        C (D p k) * (solvePair f p hp k rhs).1 +
        C (solvePair f p hp k rhs).2 * basePolynomial f p k = rhs := by
  exact Classical.choose_spec (Classical.choose_spec
    (exists_normalized_inhomogeneous_base_solution f p hp k rhs))

/-- Actual formal coefficients (p_n,b_n), where B(s)=-D_k+sum b_n s^n.
Each step uses the proved normalized polynomial inhomogeneous solver. -/
def perturbationPair (f : Family) (p : Parameters) (hp : Admissible f p)
    (k : ℕ) : ℕ → Polynomial ℂ × ℂ
  | 0 => (basePolynomial f p k, -D p k)
  | n + 1 => solvePair f p hp k
      (-perturbationOperator f p (perturbationPair f p hp k n).1 -
        ∑ i : Fin n, C (perturbationPair f p hp k (i.val+1)).2 *
          (perturbationPair f p hp k (n-i.val)).1)
termination_by n => n
decreasing_by all_goals omega

theorem perturbationPair_zero (f : Family) (p : Parameters) (hp : Admissible f p) (k : ℕ) :
    perturbationPair f p hp k 0 = (basePolynomial f p k, -D p k) := by
  rw [perturbationPair]

theorem perturbationPair_succ_spec (f : Family) (p : Parameters)
    (hp : Admissible f p) (k n : ℕ) :
    (perturbationPair f p hp k (n+1)).1.coeff 0 = 0 ∧
      GcoyHeun.L0 p.gamma p.delta (perturbationPair f p hp k (n+1)).1 -
        C (D p k) * (perturbationPair f p hp k (n+1)).1 +
        C (perturbationPair f p hp k (n+1)).2 * basePolynomial f p k =
      -perturbationOperator f p (perturbationPair f p hp k n).1 -
        ∑ i : Fin n, C (perturbationPair f p hp k (i.val+1)).2 *
          (perturbationPair f p hp k (n-i.val)).1 := by
  rw [perturbationPair]
  exact solvePair_spec f p hp k _

theorem perturbationPair_bounded (f : Family) (p : Parameters)
    (hp : Admissible f p) (k n : ℕ) :
    GcoyHeun.Bounded (k+n) (perturbationPair f p hp k n).1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [perturbationPair_zero] using basePolynomial_bounded f p k
    | succ n =>
      refine inhomogeneous_degree_bound f p hp k (k+(n+1)) (by omega)
        (perturbationPair f p hp k (n+1)).1 _
        (perturbationPair f p hp k (n+1)).2 ?_ (perturbationPair_succ_spec f p hp k n).2
      · apply GcoyHeun.bounded_sub
        · simpa [Nat.add_assoc] using GcoyHeun.bounded_neg
            (perturbationOperator_bounded f p (ih n (by omega)))
        · intro l hl
          rw [finset_sum_coeff]
          apply Finset.sum_eq_zero
          intro i hi
          rw [coeff_C_mul]
          have hb := ih (n-i.val) (by omega)
          have hzero := hb l (by omega)
          rw [hzero, mul_zero]

#print axioms perturbationPair_succ_spec
#print axioms perturbationPair_bounded

/-- All formal perturbation equations have normalized polynomial solutions with
the sharp finite-propagation bound. No analytic branch is assumed. -/
theorem exists_formal_polynomial_perturbation (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) :
    ∃ (P : ℕ → Polynomial ℂ) (b : ℕ → ℂ),
      P 0 = basePolynomial f p k ∧ b 0 = -D p k ∧
      (∀ j, GcoyHeun.Bounded (k+j) (P j)) ∧
      (∀ j, (P (j+1)).coeff 0 = 0) ∧
      (∀ n, GcoyHeun.L0 p.gamma p.delta (P (n+1)) - C (D p k) * P (n+1) +
        C (b (n+1)) * P 0 = -perturbationOperator f p (P n) -
          ∑ i : Fin n, C (b (i.val+1)) * P (n-i.val)) := by
  refine ⟨fun j => (perturbationPair f p hp k j).1,
    fun j => (perturbationPair f p hp k j).2, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [perturbationPair_zero]
  · simp only [perturbationPair_zero]
  · exact perturbationPair_bounded f p hp k
  · intro j
    exact (perturbationPair_succ_spec f p hp k j).1
  · intro n
    simpa only [perturbationPair_zero] using (perturbationPair_succ_spec f p hp k n).2

#print axioms exists_formal_polynomial_perturbation

end Heun
