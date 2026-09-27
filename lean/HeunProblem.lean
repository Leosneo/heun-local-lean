import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

/-!
# The literal local problem in Mori–Takemura, arXiv:2503.10355v3

Equations (3.5), (3.11), (3.15), recurrence (4.1), Conjecture 1 (4.30).
`LiteratureConjecture` is the target proposition, proved by
`Heun.literatureConjecture` in `HeunCompletion.lean`.
The connection coefficient is specified by actual analytic ODE solutions
and their normalized endpoint identity. It is not defined from the conjectured series.
-/

noncomputable section
open scoped Topology
open Filter

namespace Heun

inductive Family where
  | heun | confluent | reduced
  deriving DecidableEq

structure Parameters where
  gamma : ℂ
  delta : ℂ
  alpha : ℂ
  beta : ℂ
  epsilon : ℂ

def Admissible (f : Family) (p : Parameters) : Prop :=
  (∀ m : ℤ, p.gamma ≠ (m : ℂ)) ∧
  (∀ m : ℤ, p.delta ≠ (m : ℂ)) ∧
  (∀ m : ℕ, p.gamma + p.delta ≠ -(m : ℂ)) ∧
  (f = .heun → p.gamma + p.delta + p.epsilon = p.alpha + p.beta + 1)

def D (p : Parameters) (m : ℕ) : ℂ :=
  (m : ℂ) * ((m : ℂ) - 1 + p.gamma + p.delta)

def E (f : Family) (p : Parameters) (m : ℕ) : ℂ :=
  match f with
  | .heun => (m : ℂ) * ((m : ℂ) - 1 + p.gamma + p.epsilon)
  | .confluent => (m : ℂ)
  | .reduced => 0

def F (f : Family) (p : Parameters) (m : ℕ) : ℂ :=
  match f with
  | .heun => ((m : ℂ) - 1 + p.alpha) * ((m : ℂ) - 1 + p.beta)
  | .confluent => (m : ℂ) - 1 + p.alpha
  | .reduced => 1

/-- Coefficients of y' and y in the source's normalized equations. -/
def drift (f : Family) (p : Parameters) (s z : ℂ) : ℂ :=
  p.gamma / z + p.delta / (z - 1) + match f with
  | .heun => -(s * p.epsilon / (1 - s * z))
  | .confluent => -s
  | .reduced => 0

def potential (f : Family) (p : Parameters) (B s z : ℂ) : ℂ :=
  match f with
  | .heun => (B - s * p.alpha * p.beta * z) / (z * (z - 1) * (1 - s * z))
  | .confluent => (B - s * p.alpha * z) / (z * (z - 1))
  | .reduced => (B - s * z) / (z * (z - 1))

def SolvesOn (f : Family) (p : Parameters) (B s : ℂ)
    (y : ℂ → ℂ) (U : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ y U ∧ ∀ z ∈ U,
    deriv (deriv y) z + drift f p s z * deriv y z + potential f p B s z * y z = 0

def zeroDisk : Set ℂ := Metric.ball (0 : ℂ) (3 / 4 : ℝ)
def oneDisk : Set ℂ := Metric.ball (1 : ℂ) (3 / 4 : ℝ)
def overlap : Set ℂ := zeroDisk ∩ oneDisk

/-- Principal branch; on the overlap, Re (1-z)>0, so its cut is avoided. -/
def singularSolution (p : Parameters) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 - z) ^ (1 - p.delta) * h z

/-- The literature's d₂, specified by a normalized Frobenius connection identity.
All three unknown functions are actual complex-analytic functions solving the ODE.
The fixed disks suffice for local s near zero; no existence is assumed here. -/
def IsConnectionCoefficient (f : Family) (p : Parameters) (B s d₂ : ℂ) : Prop :=
  ∃ (y u h : ℂ → ℂ) (d₁ : ℂ),
    AnalyticOnNhd ℂ y zeroDisk ∧ y 0 = 1 ∧
    SolvesOn f p B s y (zeroDisk \ {0}) ∧
    AnalyticOnNhd ℂ u oneDisk ∧ u 1 = 1 ∧
    SolvesOn f p B s u (oneDisk \ {1}) ∧
    AnalyticOnNhd ℂ h oneDisk ∧ h 1 = 1 ∧
    SolvesOn f p B s (singularSolution p h) overlap ∧
    ∀ z ∈ overlap, y z = d₁ * u z + d₂ * singularSolution p h z

/-- State at index m is (c_(m-1), c_m), with initial state (0,1). -/
def coefficientPair (f : Family) (p : Parameters) (B s : ℂ) : ℕ → ℂ × ℂ
  | 0 => (0, 1)
  | m + 1 =>
    let q := coefficientPair f p B s m
    (q.2, ((B + D p m + s * E f p m) * q.2 - s * F f p m * q.1) /
      (((m : ℂ) + 1) * ((m : ℂ) + p.gamma)))

def coefficient (f : Family) (p : Parameters) (B s : ℂ) (N : ℕ) : ℂ :=
  (coefficientPair f p B s N).2

def IsFiniteRootGerm (f : Family) (p : Parameters) (k N : ℕ)
    (b : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ b 0 ∧ b 0 = -D p k ∧
    ∀ᶠ s in 𝓝 (0 : ℂ), coefficient f p (b s) s N = 0

/-- D_k^[j],(N) is minus the Taylor coefficient of the finite root B_(k,N). -/
def finiteRootTaylor (roots : ℕ → ℂ → ℂ) (N j : ℕ) : ℂ :=
  -(iteratedDeriv j (roots N) 0 / (j.factorial : ℂ))

/-- Exact local convergent-series assertion of Conjecture 1.
Finite roots, the genuine endpoint connection root, uniqueness of d₂, and
convergence are all conclusions; none is postulated as an extra hypothesis.
The radius is allowed to depend on k and the fixed parameters.
-/
def LiteratureConjecture : Prop :=
  ∀ (f : Family) (p : Parameters), Admissible f p → ∀ k : ℕ,
    ∃ (roots : ℕ → ℂ → ℂ) (b : ℂ → ℂ) (r : ℝ),
      (∀ N, k + 1 ≤ N → IsFiniteRootGerm f p k N (roots N)) ∧
      AnalyticAt ℂ b 0 ∧ b 0 = -D p k ∧ 0 < r ∧ r < 1 / 4 ∧
      ∀ s : ℂ, ‖s‖ < r →
        IsConnectionCoefficient f p (b s) s 0 ∧
        (∀ d₂, IsConnectionCoefficient f p (b s) s d₂ → d₂ = 0) ∧
        HasSum (fun j : ℕ =>
          -finiteRootTaylor roots (k + (j + 1) + 1) (j + 1) * s ^ (j + 1))
          (b s + D p k)

@[simp] theorem coefficient_zero (f p B s) : coefficient f p B s 0 = 1 := rfl

theorem E_zero (f p) : E f p 0 = 0 := by cases f <;> simp [E]

theorem coefficient_one (f p B s) : coefficient f p B s 1 = B / p.gamma := by
  simp [coefficient, coefficientPair, D, E_zero]

theorem coefficient_recurrence (f p B s) (m : ℕ) :
    coefficient f p B s (m + 2) =
      ((B + D p (m + 1) + s * E f p (m + 1)) * coefficient f p B s (m + 1) -
        s * F f p (m + 1) * coefficient f p B s m) /
      ((((m + 1 : ℕ) : ℂ) + 1) * (((m + 1 : ℕ) : ℂ) + p.gamma)) := by
  rfl

theorem coefficient_at_s_zero (f p B) (N : ℕ) :
    coefficient f p B 0 N =
      (∏ m ∈ Finset.range N, (B + D p m)) /
      (∏ m ∈ Finset.range N, (((m : ℂ) + 1) * ((m : ℂ) + p.gamma))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    change ((B + D p N + 0 * E f p N) * coefficient f p B 0 N -
      0 * F f p N * (coefficientPair f p B 0 N).1) / _ = _
    simp only [zero_mul, add_zero, sub_zero, ih, Finset.prod_range_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem coefficient_base_root (f p) {k N : ℕ} (hk : k < N) :
    coefficient f p (-D p k) 0 N = 0 := by
  rw [coefficient_at_s_zero]
  have hz : (∏ m ∈ Finset.range N, (-D p k + D p m)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hk) (by simp)
  rw [hz, zero_div]

theorem recurrence_denominator_ne_zero {f : Family} {p : Parameters}
    (hp : Admissible f p) (m : ℕ) :
    ((m : ℂ) + 1) * ((m : ℂ) + p.gamma) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Nat.succ_ne_zero m)
  · have h := hp.1 (-(m : ℤ))
    push_cast at h
    intro hz
    apply h
    linear_combination hz

theorem recurrence_denominator_ne_zero_of_nonresonant {p : Parameters}
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (m : ℕ) :
    ((m : ℂ) + 1) * ((m : ℂ) + p.gamma) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Nat.succ_ne_zero m)
  · intro hz
    apply hgamma m
    linear_combination hz

theorem D_sub (p : Parameters) (m n : ℕ) :
    D p m - D p n = ((m : ℂ) - n) * ((m : ℂ) + n - 1 + p.gamma + p.delta) := by
  unfold D
  ring

theorem D_injective {f : Family} {p : Parameters} (hp : Admissible f p) :
    Function.Injective (D p) := by
  intro m n heq
  by_contra hne
  have hsum : 1 ≤ m + n := by omega
  have hcast : (m : ℂ) - n ≠ 0 := by
    intro h
    apply hne
    exact_mod_cast (sub_eq_zero.mp h)
  have hfactor : (m : ℂ) + n - 1 + p.gamma + p.delta = 0 := by
    have h := D_sub p m n
    rw [heq, sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hcast
  apply hp.2.2.1 (m + n - 1)
  have hnat : ((m + n - 1 : ℕ) : ℂ) = (m : ℂ) + n - 1 := by
    rw [Nat.cast_sub hsum, Nat.cast_add, Nat.cast_one]
  rw [hnat]
  linear_combination hfactor

#print axioms coefficient_at_s_zero
#print axioms coefficient_base_root
#print axioms recurrence_denominator_ne_zero
#print axioms D_injective

end Heun
