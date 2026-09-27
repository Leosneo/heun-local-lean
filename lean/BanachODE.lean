import ActualConnection
import BanachSpace

noncomputable section
open scoped Topology
open Filter
namespace Heun

/-- A geometric bound of ratio one half gives analyticity throughout radius two. -/
theorem fast_series_analytic (c : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖c n‖ ≤ C * (1/2:ℝ)^n) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n, c n * z^n) (Metric.ball 0 2) := by
  intro z hz
  have hz' : ‖z‖ < (2:ℝ) := by simpa [Metric.mem_ball, dist_zero_right] using hz
  obtain ⟨r, hzr, hr⟩ := exists_between hz'
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hq : (1/2:ℝ)*r < 1 := by linarith
  have hgeo := (summable_geometric_of_lt_one (by positivity : 0 ≤ (1/2:ℝ)*r) hq).mul_left C
  have han : AnalyticOnNhd ℂ (fun w : ℂ => ∑' n, c n*w^n) (Metric.ball 0 r) := by
    apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
    apply Complex.differentiableOn_tsum_of_summable_norm hgeo
    · intro n w hw
      fun_prop
    · exact Metric.isOpen_ball
    · intro n w hw
      have hw' : ‖w‖ ≤ r := (by simpa [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < r).le
      calc
        ‖c n*w^n‖ = ‖c n‖*‖w‖^n := by simp
        _ ≤ (C*(1/2:ℝ)^n)*r^n := mul_le_mul (hc n)
          (pow_le_pow_left₀ (norm_nonneg w) hw' n) (by positivity) (by positivity)
        _ = C*((1/2:ℝ)*r)^n := by rw [mul_pow]; ring
  exact han z (by simpa [Metric.mem_ball, dist_zero_right] using hzr)

theorem fast_frobenius_analytic (f : Family) (p : Parameters) (B s : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖coefficient f p B s n‖ ≤ C*(1/2:ℝ)^n) :
    AnalyticOnNhd ℂ (frobeniusSum f p B s) (Metric.ball 0 2) :=
  fast_series_analytic _ C hC hc

/-- The cleared differential expression is analytic, including at both endpoints. -/
theorem equationValue_analytic (f : Family) (p : Parameters) (B s : ℂ)
    (y : ℂ → ℂ) {U : Set ℂ} (hy : AnalyticOnNhd ℂ y U) :
    AnalyticOnNhd ℂ (fun z => equationValue f p B s z (y z)
      (deriv y z) (deriv (deriv y) z)) U := by
  intro z hz
  have h0 := hy z hz
  have h1 := hy.deriv z hz
  have h2 := hy.deriv.deriv z hz
  cases f <;> simp only [equationValue, perturbationValue] <;> fun_prop

/-- Fast coefficients let the actual local ODE continue to the entire radius-two disk. -/
theorem fast_frobenius_cleared_ODE (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ (1/100:ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖coefficient f p B s n‖ ≤ C*(1/2:ℝ)^n) :
    ∀ z ∈ Metric.ball (0:ℂ) 2, equationValue f p B s z (frobeniusSum f p B s z)
      (deriv (frobeniusSum f p B s) z) (deriv (deriv (frobeniusSum f p B s)) z) = 0 := by
  have hy := fast_frobenius_analytic f p B s C hC hc
  have he := equationValue_analytic f p B s _ hy
  have hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ) := by
    intro n
    simpa using hp.1 (-(n:ℤ))
  have heq : (fun z => equationValue f p B s z (frobeniusSum f p B s z)
      (deriv (frobeniusSum f p B s) z) (deriv (deriv (frobeniusSum f p B s)) z))
      =ᶠ[𝓝 (0:ℂ)] (fun _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<4/5)] with z hz
    have hz' : ‖z‖ < (4/5:ℝ) := by simpa [Metric.mem_ball, dist_zero_right] using hz
    obtain ⟨h0, ha⟩ := frobenius_converges_analytic f p hg B s z hs hz'
    obtain ⟨h1,h2⟩ := frobenius_derivative_series f p hg B s z hs hz'
    exact equationValue_eq_zero f p hg hp.2.2.2 B s z _ _ _ h0.hasSum h1 h2
  exact he.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    (convex_ball (0:ℂ) (2:ℝ)).isPreconnected (by norm_num) heq

theorem fast_frobenius_source_ODE (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖coefficient f p B s n‖ ≤ C*(1/2:ℝ)^n)
    (z : ℂ) (hz : ‖z‖ < 2) (hz0 : z ≠ 0) (hz1 : z-1 ≠ 0) :
    deriv (deriv (frobeniusSum f p B s)) z +
      drift f p s z * deriv (frobeniusSum f p B s) z +
      potential f p B s z * frobeniusSum f p B s z = 0 := by
  have hsm : 1-s*z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    have hn : ‖s*z‖ < 1 := by
      rw [norm_mul]
      calc
        ‖s‖*‖z‖ ≤ (1/1000:ℝ)*‖z‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg z)
        _ < 1 := by linarith
    rw [← he, norm_one] at hn
    exact (lt_irrefl (1:ℝ)) hn
  have he := fast_frobenius_cleared_ODE f p hp B s (by linarith) C hC hc z
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  rw [equationValue_rational f p B s z _ _ _ hz0 hz1 hsm] at he
  have hd : clearedDenominator f s z ≠ 0 := by
    cases f <;> simp [clearedDenominator, hz0, hz1, hsm]
  exact (mul_eq_zero.mp he).resolve_left hd

theorem solvesOn_const_mul (f : Family) (p : Parameters) (B s : ℂ)
    (y : ℂ → ℂ) (U : Set ℂ) (hy : SolvesOn f p B s y U) (a : ℂ) :
    SolvesOn f p B s (fun z => a*y z) U := by
  refine ⟨fun z hz => analyticAt_const.mul (hy.1 z hz), ?_⟩
  intro z hz
  have hy0 := hy.1 z hz
  have h1 : deriv (fun w => a*y w) =ᶠ[𝓝 z] (fun w => a*deriv y w) := by
    filter_upwards [hy0.eventually_analyticAt] with w hw
    exact (hw.differentiableAt.hasDerivAt.const_mul a).deriv
  have h2 : deriv (deriv (fun w => a*y w)) z = a*deriv (deriv y) z := by
    rw [h1.deriv_eq]
    exact (hy0.deriv.differentiableAt.hasDerivAt.const_mul a).deriv
  rw [h2, h1.self_of_nhds]
  linear_combination a * hy.2 z hz

/-- Exponential decay plus a nonzero endpoint value gives an actual zero
connection coefficient, with every Frobenius witness constructed. -/
theorem fast_frobenius_connection_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ n, ‖coefficient f p B s n‖ ≤ C*(1/2:ℝ)^n)
    (hval : frobeniusSum f p B s 1 ≠ 0) :
    IsConnectionCoefficient f p B s 0 := by
  let y := frobeniusSum f p B s
  have ha := fast_frobenius_analytic f p B s C hC hc
  have hone : ∀ z ∈ oneDisk, ‖z‖ < (2:ℝ) := by
    intro z hz
    have hh : ‖z-1‖ < (3/4:ℝ) := by simpa [oneDisk, Metric.mem_ball, dist_eq_norm] using hz
    have ht := norm_add_le (z-1) (1:ℂ)
    simp only [sub_add_cancel, norm_one] at ht
    linarith
  have hyone : AnalyticOnNhd ℂ y oneDisk := fun z hz =>
    ha z (by simpa [Metric.mem_ball, dist_zero_right] using hone z hz)
  have hysol : SolvesOn f p B s y (oneDisk \ {1}) := by
    refine ⟨fun z hz => hyone z hz.1, ?_⟩
    intro z hz
    have hz1 : z ≠ 1 := by simpa using hz.2
    have hz0 : z ≠ 0 := by
      intro he
      have hh := hz.1
      norm_num [he, oneDisk, Metric.mem_ball] at hh
    exact fast_frobenius_source_ODE f p hp B s hs C hC hc z (hone z hz.1)
      hz0 (sub_ne_zero.mpr hz1)
  obtain ⟨hy, hy0, hyode⟩ := frobeniusSum_regular_zero_solution f p hp B s (by linarith)
  obtain ⟨hh, hh1, hvode⟩ := singularFactor_solution f p hp.2.1 hp.2.2.2 B s hs
  refine ⟨y, (fun z => (y 1)⁻¹*y z), singularFactor f p B s, y 1,
    hy, hy0, hyode, (fun z hz => analyticAt_const.mul (hyone z hz)), ?_,
    solvesOn_const_mul f p B s y _ hysol _, hh, hh1, hvode, ?_⟩
  · exact inv_mul_cancel₀ hval
  · intro z hz
    simp only [zero_mul, add_zero]
    rw [← mul_assoc, mul_inv_cancel₀ hval, one_mul]

/-- Quantitative endpoint control used to keep the normalized solution nonzero. -/
theorem fast_series_endpoint_sub_bound (c b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : Summable c) (hb : Summable b)
    (hbound : ∀ n, ‖c n-b n‖ ≤ C*(1/2:ℝ)^n) :
    ‖(∑' n, c n) - ∑' n, b n‖ ≤ 2*C := by
  rw [← hc.tsum_sub hb]
  have hg := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left C
  have hsum : Summable (fun n => ‖c n-b n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hg
  calc
    ‖∑' n, (c n-b n)‖ ≤ ∑' n, ‖c n-b n‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' n, C*(1/2:ℝ)^n := hsum.tsum_le_tsum hbound hg
    _ = 2*C := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

theorem fast_series_endpoint_ne_zero (c b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : Summable c) (hb : Summable b)
    (hbound : ∀ n, ‖c n-b n‖ ≤ C*(1/2:ℝ)^n)
    (hnear : 2*C < ‖∑' n, b n‖) : (∑' n, c n) ≠ 0 := by
  intro hz
  have h := fast_series_endpoint_sub_bound c b C hC hc hb hbound
  rw [hz, zero_sub, norm_neg] at h
  linarith

/-- The bounded sequence realization supplies the required radius-two decay. -/
theorem decode_series_analytic (x : SeqSpace) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n, decode x n*z^n) (Metric.ball 0 2) :=
  fast_series_analytic (decode x) ‖x‖ (norm_nonneg _) (decode_bound x)

theorem decode_summable (x : SeqSpace) : Summable (decode x) := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).mul_left ‖x‖)
  exact decode_bound x

@[simp] theorem decode_sub (x y : SeqSpace) (n : ℕ) :
    decode (x-y) n=decode x n-decode y n := by
  simp [decode, sub_div]

theorem decode_endpoint_sub_bound (x y : SeqSpace) :
    ‖(∑' n, decode x n)-(∑' n, decode y n)‖ ≤ 2*‖x-y‖ := by
  apply fast_series_endpoint_sub_bound _ _ _ (norm_nonneg _) (decode_summable x)
    (decode_summable y)
  intro n
  simpa only [decode_sub] using decode_bound (x-y) n

theorem decode_endpoint_ne_zero (x y : SeqSpace)
    (hnear : 2*‖x-y‖ < ‖∑' n, decode y n‖) : (∑' n, decode x n) ≠ 0 := by
  intro hz
  have h := decode_endpoint_sub_bound x y
  rw [hz, zero_sub, norm_neg] at h
  linarith

/-- A bounded recurrence solution normalized at zero is the actual Frobenius
coefficient sequence, not a separately postulated analytic solution. -/
theorem coefficient_eq_of_recurrence (f : Family) (p : Parameters)
    (hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ)) (B s : ℂ) (c : ℕ → ℂ)
    (h0 : c 0=1) (h1 : p.gamma*c 1=B)
    (hr : ∀ n : ℕ, ((n:ℂ)+2)*((n:ℂ)+1+p.gamma)*c (n+2)=
      (B+D p (n+1)+s*E f p (n+1))*c (n+1)-s*F f p (n+1)*c n) :
    ∀ n, c n=coefficient f p B s n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one =>
    rw [coefficient_one]
    apply (eq_div_iff (by simpa using hg 0)).mpr
    linear_combination h1
  | more n ih0 ih1 =>
    rw [coefficient_recurrence]
    apply (eq_div_iff (weak_denominator_ne_zero p hg (n+1))).mpr
    have h := hr n
    rw [ih0,ih1] at h
    simp only [Nat.cast_add, Nat.cast_one] at *
    linear_combination h

end Heun
#print axioms Heun.decode_endpoint_ne_zero
#print axioms Heun.coefficient_eq_of_recurrence
#print axioms Heun.fast_frobenius_connection_zero

#print axioms Heun.fast_frobenius_cleared_ODE
