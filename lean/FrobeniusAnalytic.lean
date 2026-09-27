import Integration
import FrobeniusBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Analytic convergence of the literal Heun coefficient series from a geometric
coefficient bound. The curve theorem has one complex parameter and allows B,
s, and z all to vary analytically. It is not asserted to be a theorem of joint
analyticity on a three-dimensional complex domain.
-/

noncomputable section
open scoped Topology
open Filter

namespace Heun

def frobeniusSum (f : Family) (p : Parameters) (B s z : ℂ) : ℂ :=
  ∑' n : ℕ, coefficient f p B s n * z ^ n

theorem frobenius_term_bound (f : Family) (p : Parameters) (B s z : ℂ)
    (C r : ℝ) (hC : 0 ≤ C) (_hr : 0 ≤ r)
    (hc : ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖coefficient f p B s n * z ^ n‖ ≤ C * ((5 / 4 : ℝ) * r) ^ n := by
  rw [norm_mul, norm_pow]
  calc
    ‖coefficient f p B s n‖ * ‖z‖ ^ n ≤
        (C * (5 / 4 : ℝ) ^ n) * r ^ n :=
      mul_le_mul (hc n) (pow_le_pow_left₀ (norm_nonneg z) hz n)
        (pow_nonneg (norm_nonneg z) n) (mul_nonneg hC (by positivity))
    _ = C * ((5 / 4 : ℝ) * r) ^ n := by rw [mul_pow]; ring

theorem frobenius_summable (f : Family) (p : Parameters) (B s z : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hz : ‖z‖ < (4 / 5 : ℝ)) :
    Summable (fun n : ℕ => coefficient f p B s n * z ^ n) := by
  have hq : (5 / 4 : ℝ) * ‖z‖ < 1 := by linarith
  have hgeo := (summable_geometric_of_lt_one (by positivity :
      0 ≤ (5 / 4 : ℝ) * ‖z‖) hq).mul_left C
  apply Summable.of_norm_bounded hgeo
  intro n
  exact frobenius_term_bound f p B s z C ‖z‖ hC (norm_nonneg z) hc le_rfl n

/-- Uniform geometric bounds give analyticity along any analytic parameter
curve, with all three inputs allowed to vary. -/
theorem frobeniusSum_analyticOnNhd_curve (f : Family) (p : Parameters)
    (B s z : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hB : AnalyticOnNhd ℂ B U) (hs : AnalyticOnNhd ℂ s U)
    (hz : AnalyticOnNhd ℂ z U)
    (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r) (hrsmall : r < (4 / 5 : ℝ))
    (hc : ∀ t ∈ U, ∀ n : ℕ, ‖coefficient f p (B t) (s t) n‖ ≤
      C * (5 / 4 : ℝ) ^ n)
    (hzr : ∀ t ∈ U, ‖z t‖ ≤ r) :
    AnalyticOnNhd ℂ (fun t => frobeniusSum f p (B t) (s t) (z t)) U := by
  have hq : (5 / 4 : ℝ) * r < 1 := by linarith
  have hgeo := (summable_geometric_of_lt_one (by positivity :
      0 ≤ (5 / 4 : ℝ) * r) hq).mul_left C
  apply DifferentiableOn.analyticOnNhd (s := U) _ hU
  apply Complex.differentiableOn_tsum_of_summable_norm hgeo
  · intro n t ht
    have hcoef : AnalyticAt ℂ (fun t => coefficient f p (B t) (s t) n) t :=
      (coefficient_analytic f p n (s t, B t)).comp_of_eq'
        ((hs t ht).prod (hB t ht)) rfl
    exact (hcoef.mul ((hz t ht).pow n)).differentiableAt.differentiableWithinAt
  · exact hU
  · intro n t ht
    exact frobenius_term_bound f p (B t) (s t) (z t) C r hC hr (hc t ht) (hzr t ht) n

theorem frobeniusSum_analyticAt_z (f : Family) (p : Parameters) (B s z : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hz : ‖z‖ < (4 / 5 : ℝ)) :
    AnalyticAt ℂ (frobeniusSum f p B s) z := by
  obtain ⟨r, hzr, hrsmall⟩ := exists_between hz
  have hr : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have h := frobeniusSum_analyticOnNhd_curve f p (fun _ => B) (fun _ => s)
    (fun t => t) (Metric.ball (0 : ℂ) r) Metric.isOpen_ball
    (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_const)
    (fun _ _ => analyticAt_id) C r hC hr hrsmall (fun _ _ => hc)
    (fun t ht => (by simpa [Metric.mem_ball, dist_zero_right] using ht : ‖t‖ < r).le)
  exact h z (by simpa [Metric.mem_ball, dist_zero_right] using hzr)

/-- Termwise differentiation with the coefficient index shifted to start at zero. -/
theorem hasSum_shifted_powerSeries_deriv (a : ℕ → ℂ) (r : ℝ) (z : ℂ)
    (hz : ‖z‖ < r) (u : ℕ → ℝ) (hu : Summable u)
    (hbound : ∀ n w, ‖w‖ < r → ‖a n * w ^ n‖ ≤ u n) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * a (n + 1) * z ^ n)
      (deriv (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) z) := by
  have hd := Complex.hasSum_deriv_of_summable_norm (U := Metric.ball (0 : ℂ) r)
    hu (fun n => by fun_prop) Metric.isOpen_ball
    (fun n w hw => hbound n w (by simpa [Metric.mem_ball, dist_zero_right] using hw))
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  have hder : ∀ n : ℕ, deriv (fun w : ℂ => a n * w ^ n) z =
      a n * ((n : ℂ) * z ^ (n - 1)) := by
    intro n
    simpa using (((hasDerivAt_id z).pow n).const_mul (a n)).deriv
  have hd' : HasSum (fun n : ℕ => a n * ((n : ℂ) * z ^ (n - 1)))
      (deriv (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) z) := by
    simpa only [hder] using hd
  have hs := (hasSum_nat_add_iff' 1).mpr hd'
  convert hs using 1
  · funext n
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    ring
  · simp

theorem frobenius_hasSum_deriv (f : Family) (p : Parameters) (B s z : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hz : ‖z‖ < (4 / 5 : ℝ)) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * coefficient f p B s (n + 1) * z ^ n)
      (deriv (frobeniusSum f p B s) z) := by
  obtain ⟨r, hzr, hrsmall⟩ := exists_between hz
  have hr : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hq : (5 / 4 : ℝ) * r < 1 := by linarith
  have hgeo := (summable_geometric_of_lt_one (by positivity :
      0 ≤ (5 / 4 : ℝ) * r) hq).mul_left C
  apply hasSum_shifted_powerSeries_deriv (coefficient f p B s) r z hzr _ hgeo
  intro n w hw
  exact frobenius_term_bound f p B s w C r hC hr hc hw.le n

theorem frobenius_deriv_term_bound (f : Family) (p : Parameters) (B s w : ℂ)
    (C r : ℝ) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hc : ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hw : ‖w‖ ≤ r) (n : ℕ) :
    ‖(n + 1 : ℂ) * coefficient f p B s (n + 1) * w ^ n‖ ≤
      (C * (5 / 4 : ℝ)) * ((n : ℝ) + 1) * ((5 / 4 : ℝ) * r) ^ n := by
  have hn : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by
    simpa using Complex.norm_natCast (n + 1)
  rw [norm_mul, norm_mul, hn, norm_pow]
  calc
    ((n : ℝ) + 1) * ‖coefficient f p B s (n + 1)‖ * ‖w‖ ^ n ≤
        (((n : ℝ) + 1) * (C * (5 / 4 : ℝ) ^ (n + 1))) * r ^ n :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hc (n + 1)) (by positivity))
        (pow_le_pow_left₀ (norm_nonneg w) hw n) (by positivity) (by positivity)
    _ = _ := by rw [pow_succ, mul_pow]; ring

theorem frobenius_hasSum_deriv_two (f : Family) (p : Parameters) (B s z : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hz : ‖z‖ < (4 / 5 : ℝ)) :
    HasSum (fun n : ℕ => (n + 2 : ℂ) * (n + 1 : ℂ) *
      coefficient f p B s (n + 2) * z ^ n)
      (deriv (deriv (frobeniusSum f p B s)) z) := by
  obtain ⟨r, hzr, hrsmall⟩ := exists_between hz
  have hr : 0 ≤ r := (norm_nonneg z).trans hzr.le
  let q : ℝ := (5 / 4 : ℝ) * r
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : q < 1 := by dsimp [q]; linarith
  have hg0 := summable_geometric_of_lt_one hq0 hq
  have hg1 := summable_pow_mul_geometric_of_norm_lt_one 1
    (show ‖q‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq)
  have hweight : Summable (fun n : ℕ => (C * (5 / 4 : ℝ)) *
      ((n : ℝ) + 1) * q ^ n) := by
    convert (hg1.add hg0).mul_left (C * (5 / 4 : ℝ)) using 1
    funext n
    simp only [pow_one]
    ring
  let a : ℕ → ℂ := fun n => (n + 1 : ℂ) * coefficient f p B s (n + 1)
  have hd := hasSum_shifted_powerSeries_deriv a r z hzr _ hweight
    (fun n w hw => frobenius_deriv_term_bound f p B s w C r hC hr hc hw.le n)
  have heq : (fun w : ℂ => ∑' n : ℕ, a n * w ^ n) =ᶠ[𝓝 z]
      deriv (frobeniusSum f p B s) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w hw
    exact (frobenius_hasSum_deriv f p B s w C hC hc hw).tsum_eq
  rw [heq.deriv_eq] at hd
  convert hd using 1
  funext n
  dsimp [a]
  push_cast
  ring

theorem coefficient_geometric_bound_fixedB (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖s‖ ≤ 1 / 100 →
      ∀ n : ℕ, ‖coefficient f p B s n‖ ≤ C * (5 / 4 : ℝ) ^ n := by
  obtain ⟨M₀, hM₀⟩ := exists_parameterBound p
  have hM : ParameterBound p (max M₀ ‖B‖) := by
    rcases hM₀ with ⟨h₁, hγ, hδ, hε, hα, hβ⟩
    exact ⟨h₁.trans (le_max_left _ _), hγ.trans (le_max_left _ _),
      hδ.trans (le_max_left _ _), hε.trans (le_max_left _ _),
      hα.trans (le_max_left _ _), hβ.trans (le_max_left _ _)⟩
  obtain ⟨C, hC, hc⟩ := coefficient_geometric_bound f p hgamma hM
  exact ⟨C, hC, fun s hs => hc B s (le_max_right _ _) hs⟩

/-- Unconditional local convergence and z-analyticity for the actual recurrence:
the coefficient estimate is proved, not an extra assumption. -/
theorem frobenius_converges_analytic (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B s z : ℂ)
    (hs : ‖s‖ ≤ 1 / 100) (hz : ‖z‖ < (4 / 5 : ℝ)) :
    Summable (fun n : ℕ => coefficient f p B s n * z ^ n) ∧
      AnalyticAt ℂ (frobeniusSum f p B s) z := by
  obtain ⟨C, hC, hc⟩ := coefficient_geometric_bound_fixedB f p hgamma B
  exact ⟨frobenius_summable f p B s z C hC.le (hc s hs) hz,
    frobeniusSum_analyticAt_z f p B s z C hC.le (hc s hs) hz⟩

theorem frobenius_derivative_series (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B s z : ℂ)
    (hs : ‖s‖ ≤ 1 / 100) (hz : ‖z‖ < (4 / 5 : ℝ)) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * coefficient f p B s (n + 1) * z ^ n)
      (deriv (frobeniusSum f p B s) z) ∧
    HasSum (fun n : ℕ => (n + 2 : ℂ) * (n + 1 : ℂ) *
      coefficient f p B s (n + 2) * z ^ n)
      (deriv (deriv (frobeniusSum f p B s)) z) := by
  obtain ⟨C, hC, hc⟩ := coefficient_geometric_bound_fixedB f p hgamma B
  exact ⟨frobenius_hasSum_deriv f p B s z C hC.le (hc s hs) hz,
    frobenius_hasSum_deriv_two f p B s z C hC.le (hc s hs) hz⟩

/-- Analytic dependence along bounded analytic curves, with the uniform
coefficient majorant discharged by the actual recurrence bound. -/
theorem frobenius_analytic_curve (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ))
    {M : ℝ} (hM : ParameterBound p M)
    (B s z : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hB : AnalyticOnNhd ℂ B U) (hs : AnalyticOnNhd ℂ s U)
    (hz : AnalyticOnNhd ℂ z U)
    (hBM : ∀ t ∈ U, ‖B t‖ ≤ M) (hsM : ∀ t ∈ U, ‖s t‖ ≤ 1 / 100)
    (r : ℝ) (hr : 0 ≤ r) (hrsmall : r < (4 / 5 : ℝ))
    (hzr : ∀ t ∈ U, ‖z t‖ ≤ r) :
    AnalyticOnNhd ℂ (fun t => frobeniusSum f p (B t) (s t) (z t)) U := by
  obtain ⟨C, hC, hc⟩ := coefficient_geometric_bound f p hgamma hM
  exact frobeniusSum_analyticOnNhd_curve f p B s z U hU hB hs hz C r hC.le
    hr hrsmall (fun t ht => hc (B t) (s t) (hBM t ht) (hsM t ht)) hzr

end Heun

#print axioms Heun.frobenius_summable
#print axioms Heun.frobeniusSum_analyticOnNhd_curve
#print axioms Heun.frobeniusSum_analyticAt_z
#print axioms Heun.frobenius_hasSum_deriv
#print axioms Heun.frobenius_hasSum_deriv_two
#print axioms Heun.frobenius_converges_analytic
#print axioms Heun.frobenius_derivative_series
#print axioms Heun.frobenius_analytic_curve
