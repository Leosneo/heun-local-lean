import ActualConnection
import JointAnalytic

noncomputable section
open Topology Filter
namespace Heun

theorem reflected_parameter_strict (f : Family) (s : ℂ)
    (hs : ‖s‖ < (1/1000:ℝ)) : ‖reflectedParameter f s‖ < (1/100:ℝ) := by
  have hl : 1-‖s‖ ≤ ‖1-s‖ := by simpa using norm_sub_norm_le (1:ℂ) s
  have hd : 0 < ‖1-s‖ := by linarith
  cases f with
  | heun =>
    simp only [reflectedParameter, norm_div, norm_neg]
    apply (div_lt_iff₀ hd).mpr
    linarith
  | confluent => simpa [reflectedParameter] using (show ‖s‖ < (1/100:ℝ) by linarith)
  | reduced => simpa [reflectedParameter] using (show ‖s‖ < (1/100:ℝ) by linarith)

theorem reflected_map_contDiffAt (f : Family) (p : Parameters) (B s : ℂ)
    (hs : ‖s‖ < (1/1000:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ =>
      (reflectedParameter f v.1, reflectedAccessory f p v.2 v.1)) (s,B) := by
  have hn : 1-s ≠ 0 := by
    intro he
    have h : s=1 := by linear_combination -he
    norm_num [h] at hs
  cases f <;> dsimp only [reflectedParameter, reflectedAccessory] <;>
    fun_prop (disch := assumption)

theorem regularOne_contDiffAt (f : Family) (p : Parameters)
    (hd : ∀ n : ℕ, p.delta ≠ -(n:ℂ)) (B s z : ℂ)
    (hs : ‖s‖ < (1/1000:ℝ)) (hz : ‖1-z‖ < (4/5:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => regularOne f p v.2 v.1 z) (s,B) := by
  have h := frobeniusSum_contDiffAt f (reflectedParameters p) hd
    (reflectedAccessory f p B s) (reflectedParameter f s) (1-z)
    (reflected_parameter_strict f s hs) hz
  exact h.comp (s,B) (reflected_map_contDiffAt f p B s hs)

theorem regularOneDeriv_contDiffAt (f : Family) (p : Parameters)
    (hd : ∀ n : ℕ, p.delta ≠ -(n:ℂ)) (B s z : ℂ)
    (hs : ‖s‖ < (1/1000:ℝ)) (hz : ‖1-z‖ < (4/5:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => deriv (regularOne f p v.2 v.1) z) (s,B) := by
  have h := frobeniusDeriv_contDiffAt f (reflectedParameters p) hd
    (reflectedAccessory f p B s) (reflectedParameter f s) (1-z)
    (reflected_parameter_strict f s hs) hz
  have hc := (h.comp (s,B) (reflected_map_contDiffAt f p B s hs)).neg
  convert hc using 1
  ext v
  exact deriv_comp_const_sub _ 1 z


theorem shifted_reflected_map_contDiffAt (f : Family) (p : Parameters) (B s : ℂ)
    (hs : ‖s‖ < (1/1000:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ =>
      (reflectedParameter f v.1,
       exponentShiftAccessory f (reflectedParameters p)
         (reflectedAccessory f p v.2 v.1) (reflectedParameter f v.1))) (s,B) := by
  have hn : 1-s ≠ 0 := by
    intro he
    have h : s=1 := by linear_combination -he
    norm_num [h] at hs
  cases f <;> dsimp only [reflectedParameter, reflectedAccessory, exponentShiftAccessory] <;>
    fun_prop (disch := assumption)

theorem singularFactor_contDiffAt (f : Family) (p : Parameters)
    (hd : ∀ n : ℤ, p.delta ≠ (n:ℂ)) (B s z : ℂ)
    (hs : ‖s‖ < (1/1000:ℝ)) (hz : ‖1-z‖ < (4/5:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => singularFactor f p v.2 v.1 z) (s,B) := by
  have h := frobeniusSum_contDiffAt f (exponentShiftParameters (reflectedParameters p))
    (exponentShift_nonresonant (reflectedParameters p) hd)
    (exponentShiftAccessory f (reflectedParameters p) (reflectedAccessory f p B s)
      (reflectedParameter f s)) (reflectedParameter f s) (1-z)
    (reflected_parameter_strict f s hs) hz
  exact h.comp (s,B) (shifted_reflected_map_contDiffAt f p B s hs)

theorem singularFactorDeriv_contDiffAt (f : Family) (p : Parameters)
    (hd : ∀ n : ℤ, p.delta ≠ (n:ℂ)) (B s z : ℂ)
    (hs : ‖s‖ < (1/1000:ℝ)) (hz : ‖1-z‖ < (4/5:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => deriv (singularFactor f p v.2 v.1) z) (s,B) := by
  have h := frobeniusDeriv_contDiffAt f (exponentShiftParameters (reflectedParameters p))
    (exponentShift_nonresonant (reflectedParameters p) hd)
    (exponentShiftAccessory f (reflectedParameters p) (reflectedAccessory f p B s)
      (reflectedParameter f s)) (reflectedParameter f s) (1-z)
    (reflected_parameter_strict f s hs) hz
  have hc := (h.comp (s,B) (shifted_reflected_map_contDiffAt f p B s hs)).neg
  convert hc using 1
  ext v
  change deriv (fun w : ℂ =>
    frobeniusSum f (exponentShiftParameters (reflectedParameters p))
      (exponentShiftAccessory f (reflectedParameters p) (reflectedAccessory f p v.2 v.1)
        (reflectedParameter f v.1)) (reflectedParameter f v.1) (1-w)) z = _
  exact deriv_comp_const_sub _ 1 z


theorem singularSolution_midpoint_deriv (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ)) :
    deriv (singularSolution p (singularFactor f p B s)) (1/2) =
      -(1-p.delta)*(1/2:ℂ)^((1-p.delta)-1)*singularFactor f p B s (1/2) +
      (1/2:ℂ)^(1-p.delta)*deriv (singularFactor f p B s) (1/2) := by
  have ha := (singularFactor_solution f p hp.2.1 hp.2.2.2 B s hs).1
    (1/2) overlap_midpoint.2
  have hsl : (1-(1/2:ℂ)) ∈ Complex.slitPlane := by
    exact overlap_reflected_slit overlap_midpoint
  have hc := (Complex.hasStrictDerivAt_cpow_const (c := 1-p.delta) hsl).hasDerivAt.comp
    (1/2:ℂ) ((hasDerivAt_const (1/2:ℂ) (1:ℂ)).sub (hasDerivAt_id (1/2:ℂ)))
  have ht := (hc.mul ha.differentiableAt.hasDerivAt).deriv
  change deriv (fun z => (1-z)^(1-p.delta)*singularFactor f p B s z) (1/2) = _
  change deriv (fun z => (1-z)^(1-p.delta)*singularFactor f p B s z) (1/2) = _ at ht
  rw [ht]
  norm_num
  ring

theorem singularSolutionDeriv_contDiffAt (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ < (1/1000:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ =>
      deriv (singularSolution p (singularFactor f p v.2 v.1)) (1/2)) (s,B) := by
  have h1 := singularFactor_contDiffAt f p hp.2.1 B s (1/2) hs (by norm_num)
  have h2 := singularFactorDeriv_contDiffAt f p hp.2.1 B s (1/2) hs (by norm_num)
  have h : ContDiffAt ℂ 1 (fun v : ℂ × ℂ =>
      -(1-p.delta)*(1/2:ℂ)^((1-p.delta)-1)*singularFactor f p v.2 v.1 (1/2) +
      (1/2:ℂ)^(1-p.delta)*deriv (singularFactor f p v.2 v.1) (1/2)) (s,B) :=
    (contDiffAt_const.mul h1).add (contDiffAt_const.mul h2)
  apply h.congr_of_eventuallyEq
  have he : ∀ᶠ v : ℂ × ℂ in 𝓝 (s,B), ‖v.1‖ < (1/1000:ℝ) :=
    continuousAt_fst.norm.eventually_lt_const hs
  filter_upwards [he] with v hv
  exact singularSolution_midpoint_deriv f p hp v.2 v.1 hv.le


theorem actualConnection_contDiffAt (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ < (1/1000:ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => actualConnection f p v.2 v.1) (s,B) := by
  have hd : ∀ n : ℕ, p.delta ≠ -(n:ℂ) := by
    intro n
    simpa using hp.2.1 (-(n:ℤ))
  have hg : ∀ n : ℕ, p.gamma ≠ -(n:ℂ) := by
    intro n
    simpa using hp.1 (-(n:ℤ))
  have hsmall : ‖s‖ < (1/100:ℝ) := by linarith
  have hy := frobeniusSum_contDiffAt f p hg
    B s (1/2) hsmall (by norm_num)
  have hyd := frobeniusDeriv_contDiffAt f p hg
    B s (1/2) hsmall (by norm_num)
  have hu := regularOne_contDiffAt f p hd B s (1/2) hs (by norm_num)
  have hud := regularOneDeriv_contDiffAt f p hd B s (1/2) hs (by norm_num)
  have hh := singularFactor_contDiffAt f p hp.2.1 B s (1/2) hs (by norm_num)
  have hv : ContDiffAt ℂ 1 (fun v : ℂ × ℂ =>
      singularSolution p (singularFactor f p v.2 v.1) (1/2)) (s,B) := by
    exact contDiffAt_const.mul hh
  have hvd := singularSolutionDeriv_contDiffAt f p hp B s hs
  exact ((hu.mul hyd).sub (hud.mul hy)).div
    ((hu.mul hvd).sub (hud.mul hv))
    (actual_endpoint_wronskian_ne_zero f p hp B s hs.le)

#print axioms actualConnection_contDiffAt
end Heun
