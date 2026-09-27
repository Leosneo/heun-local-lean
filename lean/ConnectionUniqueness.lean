import RegularSingularUniqueness
import EndpointIndependence

noncomputable section
open scoped Topology
open Filter

namespace Heun

/-- A singular factor with nonzero endpoint normalization cannot agree with an
endpoint-analytic function even as a germ at the ordinary midpoint. -/
theorem endpoint_singular_not_analytic (p : Parameters)
    (hdelta : ∀ m : ℤ, p.delta ≠ (m : ℂ)) (h g : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h oneDisk) (hh1 : h 1 ≠ 0)
    (hg : AnalyticOnNhd ℂ g oneDisk)
    (heq : singularSolution p h =ᶠ[𝓝 (1/2 : ℂ)] g) : False := by
  have heU := (singular_analytic_half p h hh).eqOn_of_preconnected_of_eventuallyEq
    (fun z hz => hg z hz.1) endpointHalfDisk_preconnected endpointHalfDisk_midpoint heq
  have h1mem : (1 : ℂ) ∈ oneDisk := by norm_num [oneDisk, Metric.mem_ball]
  letI := originHalfDisk_zero_neBot
  have ht : AnalyticAt ℂ (fun w : ℂ => 1-w) 0 := analyticAt_const.sub analyticAt_id
  have hhc : AnalyticAt ℂ (fun w => h (1-w)) 0 :=
    (hh 1 h1mem).comp_of_eq ht (by simp)
  have hgc : AnalyticAt ℂ (fun w => g (1-w)) 0 :=
    (hg 1 h1mem).comp_of_eq ht (by simp)
  have hex : ∀ n : ℕ, (1-p.delta : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hdelta (1-(n : ℤ))
    push_cast
    linear_combination -hn
  apply Gcoy.SingularGerm.cpow_mul_not_regularGerms originHalfDisk originHalfDisk_open
    originHalfDisk_slit (1-p.delta) hex (fun w => h (1-w)) hhc (by simpa using hh1)
  refine ⟨(fun w => g (1-w)), hgc, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  simpa [singularSolution] using heU (origin_to_endpoint_half hw)

/-- Uniqueness of the literal normalized endpoint connection coefficient,
independent of all choices of normalized Frobenius witnesses. -/
theorem isConnectionCoefficient_unique_nonresonant (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ))
    (hdelta : ∀ m : ℤ, p.delta ≠ (m : ℂ))
    (B s d d' : ℂ)
    (hd : IsConnectionCoefficient f p B s d)
    (hd' : IsConnectionCoefficient f p B s d') : d = d' := by
  rcases hd with ⟨y, u, h, a, hy, hy0, hyode, hu, hu1, huode, hh, hh1, hvode, heq⟩
  rcases hd' with ⟨y', u', h', a', hy', hy0', hyode', hu', hu1', huode',
    hh', hh1', hvode', heq'⟩
  have hyy := source_regular_zero_unique_on f p B s hgamma hy hy' hyode hyode'
    (hy0.trans hy0'.symm)
  by_contra hne
  let H : ℂ → ℂ := fun z => d' * h' z - d * h z
  let G : ℂ → ℂ := fun z => a * u z - a' * u' z
  have hH : AnalyticOnNhd ℂ H oneDisk := fun z hz =>
    (analyticAt_const.mul (hh' z hz)).sub (analyticAt_const.mul (hh z hz))
  have hG : AnalyticOnNhd ℂ G oneDisk := fun z hz =>
    (analyticAt_const.mul (hu z hz)).sub (analyticAt_const.mul (hu' z hz))
  have hH1 : H 1 ≠ 0 := by
    dsimp [H]
    rw [hh1, hh1', mul_one, mul_one]
    exact sub_ne_zero.mpr (Ne.symm hne)
  apply endpoint_singular_not_analytic p hdelta H G hH hH1 hG
  filter_upwards [overlap_open.mem_nhds overlap_midpoint] with z hz
  have h₁ := heq z hz
  have h₂ := heq' z hz
  have h₃ := hyy hz.1
  simp only [singularSolution, H, G] at *
  linear_combination h₁ - h₂ - h₃

theorem isConnectionCoefficient_unique (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s d d' : ℂ)
    (hd : IsConnectionCoefficient f p B s d)
    (hd' : IsConnectionCoefficient f p B s d') : d = d' := by
  apply isConnectionCoefficient_unique_nonresonant f p _ hp.2.1 B s d d' hd hd'
  intro n
  simpa using hp.1 (-(n : ℤ))

end Heun

#print axioms Heun.isConnectionCoefficient_unique
