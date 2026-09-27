import FiniteRootStabilization
import Integration
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open scoped Topology
open Filter PowerSeries
namespace Heun

def analyticTaylor (g : ℂ → ℂ) : Series :=
  PowerSeries.mk (fun j => iteratedDeriv j g 0 / (j.factorial : ℂ))

@[simp] theorem analyticTaylor_coeff (g : ℂ → ℂ) (j : ℕ) :
    PowerSeries.coeff j (analyticTaylor g) = iteratedDeriv j g 0 / (j.factorial : ℂ) :=
  PowerSeries.coeff_mk _ _

@[simp] theorem analyticTaylor_constantCoeff (g : ℂ → ℂ) :
    constantCoeff (analyticTaylor g) = g 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, analyticTaylor_coeff]
  simp

theorem analyticTaylor_congr {g h : ℂ → ℂ} (he : g =ᶠ[𝓝 0] h) :
    analyticTaylor g = analyticTaylor h := by
  ext j
  simp only [analyticTaylor_coeff, he.iteratedDeriv_eq j]

@[simp] theorem analyticTaylor_const (c : ℂ) :
    analyticTaylor (fun _ => c) = C c := by
  ext j
  simp only [analyticTaylor_coeff, iteratedDeriv_const, PowerSeries.coeff_C]
  split_ifs with h
  · subst j; simp
  · simp

@[simp] theorem analyticTaylor_id : analyticTaylor (fun s : ℂ => s) = X := by
  ext j
  simp only [analyticTaylor_coeff, iteratedDeriv_fun_id_zero, PowerSeries.coeff_X]
  by_cases h : j = 1
  · subst j; simp
  · simp [h]

theorem analyticTaylor_add {g h : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0) :
    analyticTaylor (fun s => g s + h s) = analyticTaylor g + analyticTaylor h := by
  ext j
  simp only [map_add, analyticTaylor_coeff,
    iteratedDeriv_fun_add hg.contDiffAt hh.contDiffAt, add_div]

theorem analyticTaylor_sub {g h : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0) :
    analyticTaylor (fun s => g s - h s) = analyticTaylor g - analyticTaylor h := by
  ext j
  simp only [map_sub, analyticTaylor_coeff,
    iteratedDeriv_fun_sub hg.contDiffAt hh.contDiffAt, sub_div]

theorem analyticTaylor_mul {g h : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0) :
    analyticTaylor (fun s => g s * h s) = analyticTaylor g * analyticTaylor h := by
  ext j
  rw [analyticTaylor_coeff, iteratedDeriv_fun_mul hg.contDiffAt hh.contDiffAt,
    PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (analyticTaylor g) * PowerSeries.coeff b (analyticTaylor h))]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [analyticTaylor_coeff]
  have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
  have hfact : (j.choose i : ℂ) * (i.factorial : ℂ) * ((j - i).factorial : ℂ) = (j.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
  have hi0 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj0 : ((j-i).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-i)
  have h0 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp
  linear_combination iteratedDeriv i g 0 * iteratedDeriv (j-i) h 0 * hfact

/-- Taylor expansion commutes with the literal coefficient recurrence. -/
theorem analyticTaylor_coefficientPair (f : Family) (p : Parameters)
    {b : ℂ → ℂ} (hb : AnalyticAt ℂ b 0) (m : ℕ) :
    (analyticTaylor (fun s => (coefficientPair f p (b s) s m).1),
     analyticTaylor (fun s => (coefficientPair f p (b s) s m).2)) =
      formalPair f p (analyticTaylor b) m := by
  induction m with
  | zero => simp [coefficientPair, formalPair]
  | succ m ih =>
    have ha : AnalyticAt ℂ (fun s => coefficientPair f p (b s) s m) 0 :=
      (coefficientPair_analytic f p m (0, b 0)).comp (f := fun s : ℂ => (s, b s)) (analyticAt_id.prod hb)
    have hfst := analyticAt_fst.comp ha
    have hsnd := analyticAt_snd.comp ha
    change AnalyticAt ℂ (fun s => (coefficientPair f p (b s) s m).1) 0 at hfst
    change AnalyticAt ℂ (fun s => (coefficientPair f p (b s) s m).2) 0 at hsnd
    have hi1 := congrArg Prod.fst ih
    have hi2 := congrArg Prod.snd ih
    dsimp only at hi1 hi2
    simp only [coefficientPair, formalPair, div_eq_mul_inv]
    apply Prod.ext hi2
    simp (disch := solve_by_elim (maxDepth := 20) [AnalyticAt.mul, AnalyticAt.add,
      AnalyticAt.sub, analyticAt_const, analyticAt_id]) only [analyticTaylor_mul, analyticTaylor_add,
      analyticTaylor_sub, analyticTaylor_const, analyticTaylor_id, hi1, hi2]

 theorem analyticTaylor_coefficient (f : Family) (p : Parameters)
    {b : ℂ → ℂ} (hb : AnalyticAt ℂ b 0) (m : ℕ) :
    analyticTaylor (fun s => coefficient f p (b s) s m) =
      formalCoefficient f p (analyticTaylor b) m :=
  congrArg Prod.snd (analyticTaylor_coefficientPair f p hb m)

 theorem analyticTaylor_finite_root {f : Family} {p : Parameters} {k N : ℕ}
    {b : ℂ → ℂ} (hb : IsFiniteRootGerm f p k N b) :
    constantCoeff (analyticTaylor b) = -D p k ∧
    formalCoefficient f p (analyticTaylor b) N = 0 := by
  constructor
  · simpa using hb.2.1
  · rw [← analyticTaylor_coefficient f p hb.1 N,
      analyticTaylor_congr hb.2.2, analyticTaylor_const, map_zero]

/-- Full stabilization for the literature's actual analytic finite roots. -/
theorem analytic_finite_root_derivatives_stabilize {f : Family} {p : Parameters}
    (hp : Admissible f p) {b t : ℂ → ℂ} {k N M j i : ℕ}
    (hb : IsFiniteRootGerm f p k N b) (ht : IsFiniteRootGerm f p k M t)
    (hN : k + j + 1 ≤ N) (hM : k + j + 1 ≤ M) (hi : i ≤ j) :
    iteratedDeriv i b 0 = iteratedDeriv i t 0 := by
  obtain ⟨hB, hrB⟩ := analyticTaylor_finite_root hb
  obtain ⟨hT, hrT⟩ := analyticTaylor_finite_root ht
  have he := formal_root_coeff_stabilization hp hB hT hrB hrT hN hM hi
  simp only [analyticTaylor_coeff] at he
  exact (div_left_inj' (by exact_mod_cast Nat.factorial_ne_zero i)).mp he

/-- The paper's signed Taylor coefficients are independent of truncation. -/
theorem finiteRootTaylor_stabilizes {f : Family} {p : Parameters}
    (hp : Admissible f p) {roots : ℕ → ℂ → ℂ} {k N M j : ℕ}
    (hNroot : IsFiniteRootGerm f p k N (roots N))
    (hMroot : IsFiniteRootGerm f p k M (roots M))
    (hN : k + j + 1 ≤ N) (hM : k + j + 1 ≤ M) :
    finiteRootTaylor roots N j = finiteRootTaylor roots M j := by
  unfold finiteRootTaylor
  rw [analytic_finite_root_derivatives_stabilize hp hNroot hMroot hN hM (le_refl j)]

/-- Polynomial support of the actual analytic normalized-solution jets. -/
theorem analytic_finite_root_solution_jet_support {f : Family} {p : Parameters}
    (hp : Admissible f p) {b : ℂ → ℂ} {k N j m : ℕ}
    (hb : IsFiniteRootGerm f p k N b) (hN : k + j + 1 ≤ N) (hm : k + j < m) :
    iteratedDeriv j (fun s => coefficient f p (b s) s m) 0 = 0 := by
  obtain ⟨hB, hrB⟩ := analyticTaylor_finite_root hb
  have he := formal_root_polynomial_jet hp hB hrB hN hm
  rw [← analyticTaylor_coefficient f p hb.1 m, analyticTaylor_coeff] at he
  exact (div_eq_zero_iff.mp he).resolve_right (by exact_mod_cast Nat.factorial_ne_zero j)

#print axioms analytic_finite_root_derivatives_stabilize
#print axioms finiteRootTaylor_stabilizes
#print axioms analytic_finite_root_solution_jet_support
end Heun
