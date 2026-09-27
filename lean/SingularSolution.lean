import FrobeniusGauge
import FrobeniusOne
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
namespace Heun

def singularFactor (f : Family) (p : Parameters) (B s z : ℂ) : ℂ :=
  let pr := reflectedParameters p
  let sr := reflectedParameter f s
  let Br := reflectedAccessory f p B s
  frobeniusSum f (exponentShiftParameters pr) (exponentShiftAccessory f pr Br sr) sr (1-z)

theorem reflected_deriv_two_unconditional (v : ℂ → ℂ) (z : ℂ) :
    deriv (deriv (fun w : ℂ => v (1-w))) z = deriv (deriv v) (1-z) := by
  have he : deriv (fun w : ℂ => v (1-w)) = fun w => -deriv v (1-w) := by
    funext w
    exact deriv_comp_const_sub v 1 w
  rw [he, deriv.fun_neg, deriv_comp_const_sub, neg_neg]

theorem overlap_reflected_slit {z : ℂ} (hz : z ∈ overlap) : 1-z ∈ Complex.slitPlane := by
  have hn : ‖z‖ < (3/4 : ℝ) := by
    simpa [zeroDisk, Metric.mem_ball, dist_zero_right] using hz.1
  have hneg : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hneg

def oneSlitDisk : Set ℂ := oneDisk ∩ {z : ℂ | 1-z ∈ Complex.slitPlane}

/-- The actual singular endpoint solution, with its normalized analytic
factor constructed from the convergent recurrence. -/
theorem singularFactor_solution_slit (f : Family) (p : Parameters)
    (hdelta : ∀ m : ℤ, p.delta ≠ (m : ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon=p.alpha+p.beta+1)
    (B s : ℂ) (hs : ‖s‖ ≤ (1/1000 : ℝ)) :
    AnalyticOnNhd ℂ (singularFactor f p B s) oneDisk ∧
      singularFactor f p B s 1 = 1 ∧
      SolvesOn f p B s (singularSolution p (singularFactor f p B s)) oneSlitDisk := by
  let pr := reflectedParameters p
  let sr := reflectedParameter f s
  let Br := reflectedAccessory f p B s
  let ps := exponentShiftParameters pr
  let Bs := exponentShiftAccessory f pr Br sr
  let h := frobeniusSum f ps Bs sr
  let v := fun t : ℂ => t^(1-pr.gamma)*h t
  have hbr : f = .heun → pr.gamma+pr.delta+pr.epsilon=pr.alpha+pr.beta+1 := by
    intro hf
    dsimp [pr, reflectedParameters]
    linear_combination hb hf
  have hbs : f = .heun → ps.gamma+ps.delta+ps.epsilon=ps.alpha+ps.beta+1 := by
    intro hf
    dsimp [ps, exponentShiftParameters]
    linear_combination hbr hf
  have hg : ∀ n : ℕ, ps.gamma ≠ -(n : ℂ) := exponentShift_nonresonant pr hdelta
  obtain ⟨ha,hnorm,hsol⟩ := frobeniusSum_regular_zero_solution_nonresonant f ps hg hbs Bs sr
    (reflected_parameter_small f s hs)
  have hfac : singularFactor f p B s = fun z => h (1-z) := rfl
  have ha1 : AnalyticOnNhd ℂ (singularFactor f p B s) oneDisk := by
    intro z hz
    rw [hfac]
    exact (ha (1-z) (reflected_mem_zeroDisk hz)).comp (analyticAt_const.sub analyticAt_id)
  have hv : singularSolution p (singularFactor f p B s) = fun z => v (1-z) := rfl
  refine ⟨ha1, ?_, ?_⟩
  · simpa [hfac, h] using hnorm
  · constructor
    · intro z hz
      exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const
        hz.2).mul (ha1 z hz.1)
    · intro z hz
      have ht := hz.2
      have ht0 := Complex.slitPlane_ne_zero ht
      have hzn : ‖z‖ < (7/4 : ℝ) := by
        have hh : ‖z-1‖ < (3/4 : ℝ) := by
          simpa [oneDisk, Metric.mem_ball, dist_eq_norm] using hz.1
        have ht := norm_add_le (z-1) (1 : ℂ)
        simp only [sub_add_cancel, norm_one] at ht
        linarith
      have hz0 : z ≠ 0 := by
        intro he
        have hh := hz.1
        norm_num [oneDisk, Metric.mem_ball, dist_eq_norm, he] at hh
      have ht1 : (1-z)-1 ≠ 0 := by simpa using neg_ne_zero.mpr hz0
      have hs1 : 1-s ≠ 0 := by
        intro he
        have he' : s=1 := by linear_combination -he
        norm_num [he'] at hs
      have hsm : 1-s*z ≠ 0 := by
        intro he
        have he' : s*z=1 := (sub_eq_zero.mp he).symm
        have hn : ‖s*z‖ ≤ (1/1000 : ℝ)*‖z‖ := by
          rw [norm_mul]; gcongr
        rw [he', norm_one] at hn
        linarith
      have hsrm : 1-sr*(1-z) ≠ 0 := by
        have htball : ‖1-z‖ < (3/4 : ℝ) := by
          simpa [zeroDisk, Metric.mem_ball, dist_zero_right] using reflected_mem_zeroDisk hz.1
        have hsr := reflected_parameter_small f s hs
        change ‖sr‖ ≤ (1/100 : ℝ) at hsr
        intro he
        have he' : sr*(1-z)=1 := (sub_eq_zero.mp he).symm
        have hn : ‖sr*(1-z)‖ ≤ (1/100 : ℝ)*‖1-z‖ := by rw [norm_mul]; gcongr
        rw [he', norm_one] at hn
        linarith
      have heq := exponentShift_solution_identity f pr hbr Br sr (1-z) h
        (ha (1-z) (reflected_mem_zeroDisk hz.1)) ht ht1 hsrm
      have hsolz := hsol.2 (1-z) ⟨reflected_mem_zeroDisk hz.1, by simpa using ht0⟩
      change deriv (deriv h) (1-z) + drift f ps sr (1-z)*deriv h (1-z) +
        potential f ps Bs sr (1-z)*h (1-z) = 0 at hsolz
      change deriv (deriv v) (1-z) + drift f pr sr (1-z)*deriv v (1-z) +
        potential f pr Br sr (1-z)*v (1-z) = _ at heq
      rw [hsolz, mul_zero] at heq
      have hdr := reflected_drift f p s (1-z) ht0 ht1 hs1 (by simpa using hsm)
      have hpot := reflected_potential f p B s (1-z) ht0 ht1 hs1 (by simpa using hsm)
      simp only [sub_sub_cancel] at hdr hpot
      rw [hv, reflected_deriv_two_unconditional, deriv_comp_const_sub]
      change drift f pr sr (1-z) = _ at hdr
      change potential f pr Br sr (1-z) = _ at hpot
      rw [hdr, hpot] at heq
      linear_combination heq

theorem singularFactor_solution (f : Family) (p : Parameters)
    (hdelta : ∀ m : ℤ, p.delta ≠ (m : ℂ))
    (hb : f = .heun → p.gamma+p.delta+p.epsilon=p.alpha+p.beta+1)
    (B s : ℂ) (hs : ‖s‖ ≤ (1/1000 : ℝ)) :
    AnalyticOnNhd ℂ (singularFactor f p B s) oneDisk ∧
      singularFactor f p B s 1 = 1 ∧
      SolvesOn f p B s (singularSolution p (singularFactor f p B s)) overlap := by
  obtain ⟨ha, hn, hsol⟩ := singularFactor_solution_slit f p hdelta hb B s hs
  refine ⟨ha, hn, ?_, ?_⟩
  · intro z hz
    exact hsol.1 z ⟨hz.2, overlap_reflected_slit hz⟩
  · intro z hz
    exact hsol.2 z ⟨hz.2, overlap_reflected_slit hz⟩

end Heun
#print axioms Heun.singularFactor_solution
