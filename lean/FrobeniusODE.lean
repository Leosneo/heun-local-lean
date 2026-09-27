import OperatorBridge
import FrobeniusAnalytic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! From actual summable derivative series to the literal Heun ODE. -/
noncomputable section
open scoped Topology

namespace Heun

def shiftTerm (z : ℂ) (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n+1 => z * a n

theorem hasSum_shiftTerm {a : ℕ → ℂ} {A : ℂ} (ha : HasSum a A) (z : ℂ) :
    HasSum (shiftTerm z a) (z*A) := by
  have h : HasSum (fun n => shiftTerm z a (n+1)) (z*A) := ha.mul_left z
  simpa [shiftTerm] using (hasSum_nat_add_iff 1).mp h

def term0 (c : ℕ → ℂ) (z : ℂ) (n : ℕ) := c n * z^n
def term1 (c : ℕ → ℂ) (z : ℂ) (n : ℕ) := ((n:ℂ)+1) * c (n+1) * z^n
def term2 (c : ℕ → ℂ) (z : ℂ) (n : ℕ) :=
  ((n:ℂ)+2) * ((n:ℂ)+1) * c (n+2) * z^n

def unperturbedTerm (p : Parameters) (c : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  shiftTerm z (shiftTerm z (term2 c z)) n - shiftTerm z (term2 c z) n +
    (p.gamma+p.delta) * shiftTerm z (term1 c z) n - p.gamma * term1 c z n

def perturbationTerm (f : Family) (p : Parameters) (c : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  match f with
  | .heun =>
    -shiftTerm z (shiftTerm z (shiftTerm z (term2 c z))) n +
      shiftTerm z (shiftTerm z (term2 c z)) n -
      (p.gamma+p.delta+p.epsilon) * shiftTerm z (shiftTerm z (term1 c z)) n +
      (p.gamma+p.epsilon) * shiftTerm z (term1 c z) n -
      p.alpha*p.beta * shiftTerm z (term0 c z) n
  | .confluent => -shiftTerm z (shiftTerm z (term1 c z)) n +
      shiftTerm z (term1 c z) n - p.alpha * shiftTerm z (term0 c z) n
  | .reduced => -shiftTerm z (term0 c z) n

def equationTerm (f : Family) (p : Parameters) (B s : ℂ)
    (c : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  unperturbedTerm p c z n + s * perturbationTerm f p c z n + B * term0 c z n

theorem equationTerm_zero_index (f : Family) (p : Parameters) (B s z : ℂ) (c : ℕ → ℂ) :
    equationTerm f p B s c z 0 = B*c 0 - p.gamma*c 1 := by
  cases f <;> simp [equationTerm, unperturbedTerm, perturbationTerm, shiftTerm,
    term0, term1] <;> ring

theorem equationTerm_succ (f : Family) (p : Parameters)
    (hb : f = .heun → p.gamma+p.delta+p.epsilon = p.alpha+p.beta+1)
    (B s z : ℂ) (c : ℕ → ℂ) (n : ℕ) :
    equationTerm f p B s c z (n+1) =
      ((B+D p (n+1)+s*E f p (n+1))*c (n+1) - s*F f p (n+1)*c n -
        ((n:ℂ)+2)*((n:ℂ)+1+p.gamma)*c (n+2)) * z^(n+1) := by
  cases n with
  | zero =>
    cases f <;> simp [equationTerm, unperturbedTerm, perturbationTerm, shiftTerm,
      term0, term1, term2, D, E, F, pow_succ] <;> ring
  | succ n =>
    cases n with
    | zero =>
      cases f <;> simp [equationTerm, unperturbedTerm, perturbationTerm, shiftTerm,
        term0, term1, term2, D, E, F, pow_succ] <;>
        first | (solve | ring) | linear_combination -(c 1 * s * z^2) * hb rfl
    | succ n =>
      cases f <;> simp [equationTerm, unperturbedTerm, perturbationTerm, shiftTerm,
        term0, term1, term2, D, E, F, pow_succ, Nat.cast_add, Nat.cast_one] <;>
        first | (solve | ring) | linear_combination -((n+2:ℂ)*c (n+2)*s*z^(n+3)) * hb rfl

theorem weak_denominator_ne_zero (p : Parameters)
    (hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ)) (n : ℕ) :
    ((n:ℂ)+1)*((n:ℂ)+p.gamma) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast Nat.succ_ne_zero n
  · intro h
    apply hg n
    linear_combination h

theorem actual_equationTerm_zero (f : Family) (p : Parameters)
    (hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon = p.alpha+p.beta+1)
    (B s z : ℂ) (n : ℕ) : equationTerm f p B s (coefficient f p B s) z n = 0 := by
  cases n with
  | zero =>
    rw [equationTerm_zero_index, coefficient_zero, coefficient_one]
    have hg0 : p.gamma ≠ 0 := by simpa using hg 0
    field_simp
    ring
  | succ n =>
    rw [equationTerm_succ f p hb]
    have hr := (eq_div_iff (weak_denominator_ne_zero p hg (n+1))).mp
      (coefficient_recurrence f p B s n)
    simp only [Nat.cast_add, Nat.cast_one] at hr
    have he : (B+D p (n+1)+s*E f p (n+1))*coefficient f p B s (n+1) -
      s*F f p (n+1)*coefficient f p B s n -
      ((n:ℂ)+2)*((n:ℂ)+1+p.gamma)*coefficient f p B s (n+2) = 0 := by
      linear_combination -hr
    rw [he, zero_mul]

def perturbationValue (f : Family) (p : Parameters) (z y y1 y2 : ℂ) : ℂ :=
  match f with
  | .heun => -(z*(z*(z*y2))) + z*(z*y2) -
      (p.gamma+p.delta+p.epsilon)*(z*(z*y1)) +
      (p.gamma+p.epsilon)*(z*y1) - p.alpha*p.beta*(z*y)
  | .confluent => -(z*(z*y1)) + z*y1 - p.alpha*(z*y)
  | .reduced => -(z*y)

def equationValue (f : Family) (p : Parameters) (B s z y y1 y2 : ℂ) : ℂ :=
  (z*(z*y2) - z*y2 + (p.gamma+p.delta)*(z*y1) - p.gamma*y1) +
    s*perturbationValue f p z y y1 y2 + B*y

theorem hasSum_perturbationTerm (f : Family) (p : Parameters)
    (c : ℕ → ℂ) (z y y1 y2 : ℂ)
    (h0 : HasSum (term0 c z) y) (h1 : HasSum (term1 c z) y1)
    (h2 : HasSum (term2 c z) y2) :
    HasSum (perturbationTerm f p c z) (perturbationValue f p z y y1 y2) := by
  have h0s := hasSum_shiftTerm h0 z
  have h1s := hasSum_shiftTerm h1 z
  have h1ss := hasSum_shiftTerm h1s z
  have h2s := hasSum_shiftTerm h2 z
  have h2ss := hasSum_shiftTerm h2s z
  have h2sss := hasSum_shiftTerm h2ss z
  cases f with
  | heun =>
    exact ((((h2sss.neg.add h2ss).sub (h1ss.mul_left (p.gamma+p.delta+p.epsilon))).add
      (h1s.mul_left (p.gamma+p.epsilon))).sub (h0s.mul_left (p.alpha*p.beta)))
  | confluent => exact (h1ss.neg.add h1s).sub (h0s.mul_left p.alpha)
  | reduced => exact h0s.neg

theorem hasSum_equationTerm (f : Family) (p : Parameters) (B s : ℂ)
    (c : ℕ → ℂ) (z y y1 y2 : ℂ)
    (h0 : HasSum (term0 c z) y) (h1 : HasSum (term1 c z) y1)
    (h2 : HasSum (term2 c z) y2) :
    HasSum (equationTerm f p B s c z) (equationValue f p B s z y y1 y2) := by
  have h1s := hasSum_shiftTerm h1 z
  have h2s := hasSum_shiftTerm h2 z
  have h2ss := hasSum_shiftTerm h2s z
  have hb := ((h2ss.sub h2s).add (h1s.mul_left (p.gamma+p.delta))).sub
    (h1.mul_left p.gamma)
  exact (hb.add ((hasSum_perturbationTerm f p c z y y1 y2 h0 h1 h2).mul_left s)).add
    (h0.mul_left B)

theorem equationValue_eq_zero (f : Family) (p : Parameters)
    (hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon = p.alpha+p.beta+1)
    (B s z y y1 y2 : ℂ)
    (h0 : HasSum (term0 (coefficient f p B s) z) y)
    (h1 : HasSum (term1 (coefficient f p B s) z) y1)
    (h2 : HasSum (term2 (coefficient f p B s) z) y2) :
    equationValue f p B s z y y1 y2 = 0 := by
  have h := hasSum_equationTerm f p B s (coefficient f p B s) z y y1 y2 h0 h1 h2
  have heq : equationTerm f p B s (coefficient f p B s) z = fun _ => 0 := by
    funext n
    exact actual_equationTerm_zero f p hg hb B s z n
  rw [heq] at h
  exact h.unique hasSum_zero

theorem equationValue_rational (f : Family) (p : Parameters) (B s z y y1 y2 : ℂ)
    (hz : z ≠ 0) (hz1 : z-1 ≠ 0) (hsm : 1-s*z ≠ 0) :
    equationValue f p B s z y y1 y2 =
      clearedDenominator f s z * (y2 + drift f p s z*y1 + potential f p B s z*y) := by
  have hsm' : 1-z*s ≠ 0 := by simpa [mul_comm] using hsm
  cases f <;> simp [equationValue, perturbationValue, clearedDenominator, drift, potential] <;>
    field_simp [hz, hz1, hsm, hsm'] <;> ring

/-- Genuine series sums obey the rational differential equation. The analytic
derivative-series theorems supply y1 and y2; no ODE identity is assumed. -/
theorem source_ODE_of_derivative_series (f : Family) (p : Parameters)
    (hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon = p.alpha+p.beta+1)
    (B s z y y1 y2 : ℂ) (hz : z ≠ 0) (hz1 : z-1 ≠ 0) (hsm : 1-s*z ≠ 0)
    (h0 : HasSum (term0 (coefficient f p B s) z) y)
    (h1 : HasSum (term1 (coefficient f p B s) z) y1)
    (h2 : HasSum (term2 (coefficient f p B s) z) y2) :
    y2 + drift f p s z*y1 + potential f p B s z*y = 0 := by
  have h := equationValue_eq_zero f p hg hb B s z y y1 y2 h0 h1 h2
  rw [equationValue_rational f p B s z y y1 y2 hz hz1 hsm] at h
  have hd : clearedDenominator f s z ≠ 0 := by
    cases f <;> simp [clearedDenominator, hz, hz1, hsm]
  exact (mul_eq_zero.mp h).resolve_left hd

#print axioms source_ODE_of_derivative_series

theorem frobeniusSum_normalized (f : Family) (p : Parameters) (B s : ℂ) :
    frobeniusSum f p B s 0 = 1 := by
  rw [frobeniusSum, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem frobeniusSum_source_ODE (f : Family) (p : Parameters)
    (hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon = p.alpha+p.beta+1)
    (B s z : ℂ) (hs : ‖s‖ ≤ 1/100) (hzsmall : ‖z‖ < (4/5:ℝ))
    (hz : z ≠ 0) (hz1 : z-1 ≠ 0) (hsm : 1-s*z ≠ 0) :
    deriv (deriv (frobeniusSum f p B s)) z +
      drift f p s z * deriv (frobeniusSum f p B s) z +
      potential f p B s z * frobeniusSum f p B s z = 0 := by
  obtain ⟨hsum, _⟩ := frobenius_converges_analytic f p hg B s z hs hzsmall
  obtain ⟨h1, h2⟩ := frobenius_derivative_series f p hg B s z hs hzsmall
  exact source_ODE_of_derivative_series f p hg hb B s z _ _ _ hz hz1 hsm
    hsum.hasSum h1 h2

/-- The actual convergent series is the normalized regular endpoint solution.
Convergence, analyticity and the ODE are proved, not hypotheses of this theorem. -/
theorem frobeniusSum_regular_zero_solution_nonresonant (f : Family) (p : Parameters)
    (hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon = p.alpha+p.beta+1)
    (B s : ℂ) (hs : ‖s‖ ≤ 1/100) :
    AnalyticOnNhd ℂ (frobeniusSum f p B s) zeroDisk ∧
      frobeniusSum f p B s 0 = 1 ∧
      SolvesOn f p B s (frobeniusSum f p B s) (zeroDisk \ {0}) := by
  have ha : AnalyticOnNhd ℂ (frobeniusSum f p B s) zeroDisk := by
    intro z hz
    have hzn : ‖z‖ < (3/4:ℝ) := by simpa [zeroDisk, Metric.mem_ball, dist_zero_right] using hz
    exact (frobenius_converges_analytic f p hg B s z hs (by linarith)).2
  refine ⟨ha, frobeniusSum_normalized f p B s, ?_⟩
  constructor
  · intro z hz
    exact ha z hz.1
  · intro z hz
    have hzn : ‖z‖ < (3/4:ℝ) := by
      simpa [zeroDisk, Metric.mem_ball, dist_zero_right] using hz.1
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hz1 : z-1 ≠ 0 := by
      intro h
      have he : z = 1 := sub_eq_zero.mp h
      norm_num [he] at hzn
    have hsm : 1-s*z ≠ 0 := by
      intro h
      have he : s*z = 1 := (sub_eq_zero.mp h).symm
      have hnorm : ‖s*z‖ ≤ (1/100:ℝ)*‖z‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hs (norm_nonneg z)
      rw [he, norm_one] at hnorm
      linarith
    exact frobeniusSum_source_ODE f p hg hb B s z hs (by linarith) hz0 hz1 hsm

theorem frobeniusSum_regular_zero_solution (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ 1/100) :
    AnalyticOnNhd ℂ (frobeniusSum f p B s) zeroDisk ∧
      frobeniusSum f p B s 0 = 1 ∧
      SolvesOn f p B s (frobeniusSum f p B s) (zeroDisk \ {0}) := by
  apply frobeniusSum_regular_zero_solution_nonresonant f p _ hp.2.2.2 B s hs
  intro n
  simpa using hp.1 (-(n:ℤ))

#print axioms frobeniusSum_regular_zero_solution

end Heun
