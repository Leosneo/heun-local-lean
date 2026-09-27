import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Simple roots of the unperturbed finite Heun coefficient

This file proves the exact finite-product derivative calculation needed at
`s = 0`. It assumes no existence of a perturbed root or connection solution.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace MoriTakemura

/-- The unscaled numerator of the source's coefficient at zero perturbation. -/
def rootProduct {K : Type*} [CommRing K] {ι : Type*}
    (S : Finset ι) (D : ι → K) : K[X] :=
  ∏ i ∈ S, (X + C (D i))

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- At a selected root, only its own differentiated factor survives. -/
theorem rootProduct_derivative_eval (S : Finset ι) (D : ι → K)
    {k : ι} (hk : k ∈ S) :
    (rootProduct S D).derivative.eval (-D k) =
      ∏ i ∈ S.erase k, (D i - D k) := by
  have hfactor : rootProduct S D =
      (X + C (D k)) * ∏ i ∈ S.erase k, (X + C (D i)) := by
    exact (Finset.mul_prod_erase S (fun i => (X + C (D i) : K[X])) hk).symm
  rw [hfactor, derivative_mul]
  simp [Polynomial.eval_prod, sub_eq_add_neg, add_comm]

/-- Pairwise distinct diagonal values make every selected product root simple. -/
theorem rootProduct_derivative_ne_zero (S : Finset ι) (D : ι → K)
    (hdistinct : Set.InjOn D (S : Set ι)) {k : ι} (hk : k ∈ S) :
    (rootProduct S D).derivative.eval (-D k) ≠ 0 := by
  rw [rootProduct_derivative_eval S D hk]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  intro heq
  have hik : i = k := hdistinct (Finset.mem_erase.mp hi).2 hk heq
  exact (Finset.mem_erase.mp hi).1 hik

/-- Exact derivative after dividing by the nonzero source denominator. -/
theorem scaled_rootProduct_derivative (S : Finset ι) (D : ι → K)
    {k : ι} (hk : k ∈ S) (denominator : K) :
    (C denominator⁻¹ * rootProduct S D).derivative.eval (-D k) =
      (∏ i ∈ S.erase k, (D i - D k)) / denominator := by
  rw [derivative_mul]
  simp [rootProduct_derivative_eval S D hk, div_eq_mul_inv, mul_comm]

/-- Simplicity survives the normalization in equation (4.2). -/
theorem scaled_rootProduct_derivative_ne_zero (S : Finset ι) (D : ι → K)
    (hdistinct : Set.InjOn D (S : Set ι)) {k : ι} (hk : k ∈ S)
    {denominator : K} (hden : denominator ≠ 0) :
    (C denominator⁻¹ * rootProduct S D).derivative.eval (-D k) ≠ 0 := by
  rw [scaled_rootProduct_derivative S D hk]
  apply div_ne_zero _ hden
  rw [← rootProduct_derivative_eval S D hk]
  exact rootProduct_derivative_ne_zero S D hdistinct hk

/-- Analytic derivative version directly usable by a complex implicit-function
argument. The derivative value is the explicit finite product above. -/
theorem complex_scaled_product_hasDerivAt (S : Finset ι) (D : ι → ℂ)
    {k : ι} (hk : k ∈ S) (denominator : ℂ) :
    HasDerivAt (fun B : ℂ => (∏ i ∈ S, (B + D i)) / denominator)
      ((∏ i ∈ S.erase k, (D i - D k)) / denominator) (-D k) := by
  have h := (C denominator⁻¹ * rootProduct S D).hasDerivAt (-D k)
  rw [scaled_rootProduct_derivative S D hk] at h
  simpa [rootProduct, Polynomial.eval_prod, div_eq_mul_inv, mul_comm] using h

/-- The source's condition on gamma + delta gives genuinely pairwise
 distinct D_m, not merely distinct neighboring values. -/
theorem quadratic_diagonal_injective (c : ℂ)
    (hc : ∀ m : ℕ, c ≠ -(m : ℂ)) :
    Function.Injective (fun n : ℕ => (n : ℂ) * ((n : ℂ) - 1 + c)) := by
  intro m n heq
  by_contra hmn
  have hsum : 1 ≤ m + n := by omega
  have hfactor : ((m : ℂ) - (n : ℂ)) *
      ((m : ℂ) + (n : ℂ) - 1 + c) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · apply hmn
    exact_mod_cast sub_eq_zero.mp hzero
  · apply hc (m + n - 1)
    have hcast : ((m + n - 1 : ℕ) : ℂ) = (m : ℂ) + (n : ℂ) - 1 := by
      rw [Nat.cast_sub hsum]
      push_cast
      rfl
    rw [hcast]
    linear_combination hzero

/-- None of the recurrence normalization factors vanishes when gamma is
not a nonpositive integer. -/
theorem recurrence_denominator_ne_zero (gamma : ℂ)
    (hgamma : ∀ m : ℕ, gamma ≠ -(m : ℂ)) (N : ℕ) :
    (∏ m ∈ Finset.range N, (((m : ℂ) + 1) * ((m : ℂ) + gamma))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro m hm
  apply mul_ne_zero
  · have hnat : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    simpa using hnat
  · intro hzero
    apply hgamma m
    linear_combination hzero

end MoriTakemura
