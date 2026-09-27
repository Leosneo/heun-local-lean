import FrobeniusODE
import FrobeniusTransform

/-! The actual normalized regular Frobenius solution at the endpoint one. -/
noncomputable section
open scoped Topology
open Filter
namespace Heun

theorem reflected_mem_zeroDisk {z : ℂ} (hz : z ∈ oneDisk) : 1-z ∈ zeroDisk := by
  simpa [zeroDisk, oneDisk, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz

theorem reflected_deriv (u : ℂ → ℂ) (ha : AnalyticOnNhd ℂ u zeroDisk)
    {z : ℂ} (hz : z ∈ oneDisk) :
    deriv (fun w : ℂ => u (1-w)) z = -deriv u (1-z) := by
  have h := (ha (1-z) (reflected_mem_zeroDisk hz)).differentiableAt.hasDerivAt.comp z
    ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z))
  simpa using h.deriv

theorem reflected_deriv_two (u : ℂ → ℂ) (ha : AnalyticOnNhd ℂ u zeroDisk)
    {z : ℂ} (hz : z ∈ oneDisk) :
    deriv (deriv (fun w : ℂ => u (1-w))) z = deriv (deriv u) (1-z) := by
  have he : deriv (fun w : ℂ => u (1-w)) =ᶠ[𝓝 z] (fun w => -deriv u (1-w)) := by
    filter_upwards [(show IsOpen oneDisk from Metric.isOpen_ball).mem_nhds hz] with w hw
    exact reflected_deriv u ha hw
  rw [he.deriv_eq]
  have h := ((ha (1-z) (reflected_mem_zeroDisk hz)).deriv.differentiableAt.hasDerivAt.comp z
    ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z))).neg
  simpa using h.deriv

theorem reflected_parameter_small (f : Family) (s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ)) :
    ‖reflectedParameter f s‖ ≤ (1/100:ℝ) := by
  have hl : 1-‖s‖ ≤ ‖1-s‖ := by simpa using norm_sub_norm_le (1:ℂ) s
  have hd : 0 < ‖1-s‖ := by linarith
  cases f with
  | heun =>
    simp only [reflectedParameter, norm_div, norm_neg]
    apply (div_le_iff₀ hd).mpr
    linarith
  | confluent => simpa [reflectedParameter] using (show ‖s‖ ≤ (1/100:ℝ) by linarith)
  | reduced => simpa [reflectedParameter] using (show ‖s‖ ≤ (1/100:ℝ) by linarith)

def regularOne (f : Family) (p : Parameters) (B s z : ℂ) : ℂ :=
  frobeniusSum f (reflectedParameters p) (reflectedAccessory f p B s)
    (reflectedParameter f s) (1-z)

theorem regularOne_solution (f : Family) (p : Parameters)
    (hdelta : ∀ n : ℕ, p.delta ≠ -(n:ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon=p.alpha+p.beta+1)
    (B s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ)) :
    AnalyticOnNhd ℂ (regularOne f p B s) oneDisk ∧ regularOne f p B s 1 = 1 ∧
      SolvesOn f p B s (regularOne f p B s) (oneDisk \ {1}) := by
  have hbr : f = .heun →
      (reflectedParameters p).gamma+(reflectedParameters p).delta+(reflectedParameters p).epsilon =
      (reflectedParameters p).alpha+(reflectedParameters p).beta+1 := by
    intro hf
    dsimp [reflectedParameters]
    linear_combination hb hf
  obtain ⟨ha, hnorm, hsol⟩ := frobeniusSum_regular_zero_solution_nonresonant f
    (reflectedParameters p) hdelta hbr (reflectedAccessory f p B s)
    (reflectedParameter f s) (reflected_parameter_small f s hs)
  let u := frobeniusSum f (reflectedParameters p) (reflectedAccessory f p B s)
    (reflectedParameter f s)
  have hu : AnalyticOnNhd ℂ u zeroDisk := ha
  have ha1 : AnalyticOnNhd ℂ (regularOne f p B s) oneDisk := by
    intro z hz
    exact (ha (1-z) (reflected_mem_zeroDisk hz)).comp (analyticAt_const.sub analyticAt_id)
  refine ⟨ha1, ?_, ?_⟩
  · simpa [regularOne] using hnorm
  · constructor
    · intro z hz
      exact ha1 z hz.1
    · intro z hz
      have hz1 : z ≠ 1 := by simpa using hz.2
      have ht : 1-z ≠ 0 := by intro h; exact hz1 (by linear_combination -h)
      have ht1 : (1-z)-1 ≠ 0 := by
        intro h
        have he : z = 0 := by linear_combination -h
        have hball := hz.1
        norm_num [oneDisk, Metric.mem_ball, dist_eq_norm, he] at hball
      have hs1 : 1-s ≠ 0 := by
        intro h
        have he : s = 1 := by linear_combination -h
        norm_num [he] at hs
      have hzn : ‖z‖ < (7/4:ℝ) := by
        have hball : ‖z-1‖ < (3/4:ℝ) := by
          simpa [oneDisk, Metric.mem_ball, dist_eq_norm] using hz.1
        have he : z = (z-1)+1 := by ring
        have hn := norm_add_le (z-1) (1:ℂ)
        rw [← he, norm_one] at hn
        linarith
      have hsm : 1-s*z ≠ 0 := by
        intro h
        have he : s*z = 1 := (sub_eq_zero.mp h).symm
        have hn : ‖s*z‖ ≤ (1/1000:ℝ)*‖z‖ := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hs (norm_nonneg z)
        rw [he, norm_one] at hn
        linarith
      have hsolz := hsol.2 (1-z) ⟨reflected_mem_zeroDisk hz.1, by simpa using ht⟩
      have hdr := reflected_drift f p s (1-z) ht ht1 hs1 (by simpa using hsm)
      have hpot := reflected_potential f p B s (1-z) ht ht1 hs1 (by simpa using hsm)
      simp only [sub_sub_cancel] at hdr hpot
      change deriv (deriv (fun w => u (1-w))) z + drift f p s z *
        deriv (fun w => u (1-w)) z + potential f p B s z * u (1-z) = 0
      rw [reflected_deriv_two u hu hz.1, reflected_deriv u hu hz.1]
      rw [hdr, hpot] at hsolz
      change deriv (deriv u) (1-z) + (-drift f p s z)*deriv u (1-z) +
        potential f p B s z*u (1-z) = 0 at hsolz
      linear_combination hsolz

#print axioms regularOne_solution
end Heun
