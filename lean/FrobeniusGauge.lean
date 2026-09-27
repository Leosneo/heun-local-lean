import FrobeniusTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open scoped Topology
namespace Heun

theorem cpow_mul_deriv (h : ℂ → ℂ) (r z : ℂ)
    (hh : AnalyticAt ℂ h z) (hz : z ∈ Complex.slitPlane) :
    deriv (fun w : ℂ => w^r*h w) z =
      r*z^(r-1)*h z + z^r*deriv h z := by
  exact ((Complex.hasStrictDerivAt_cpow_const hz).hasDerivAt.mul
    hh.differentiableAt.hasDerivAt).deriv

theorem cpow_mul_second_deriv (h : ℂ → ℂ) (r z : ℂ)
    (hh : AnalyticAt ℂ h z) (hz : z ∈ Complex.slitPlane) :
    deriv (deriv (fun w : ℂ => w^r*h w)) z =
      r*(r-1)*z^(r-2)*h z + 2*r*z^(r-1)*deriv h z +
        z^r*deriv (deriv h) z := by
  have he : deriv (fun w : ℂ => w^r*h w) =ᶠ[𝓝 z]
      (fun w : ℂ => r*w^(r-1)*h w + w^r*deriv h w) := by
    filter_upwards [hh.eventually_analyticAt, Complex.isOpen_slitPlane.mem_nhds hz] with w hw hwz
    exact cpow_mul_deriv h r w hw hwz
  rw [he.deriv_eq]
  have hd := (((Complex.hasStrictDerivAt_cpow_const (c := r-1) hz).hasDerivAt.const_mul r).mul
    hh.differentiableAt.hasDerivAt).add
    ((Complex.hasStrictDerivAt_cpow_const (c := r) hz).hasDerivAt.mul
      hh.deriv.differentiableAt.hasDerivAt)
  have hd' := hd.deriv
  change deriv (fun w : ℂ => r*w^(r-1)*h w + w^r*deriv h w) z = _ at hd'
  rw [hd']
  have hr : r-1-1 = r-2 := by ring
  rw [hr]
  ring

/-- Multiplication by z^(1-gamma) converts the shifted equation into
the original equation on the principal slit plane. -/
theorem exponentShift_solution_identity (f : Family) (p : Parameters)
    (hb : f = .heun → p.gamma+p.delta+p.epsilon=p.alpha+p.beta+1)
    (B s z : ℂ) (h : ℂ → ℂ) (hh : AnalyticAt ℂ h z)
    (hz : z ∈ Complex.slitPlane) (hz1 : z-1 ≠ 0) (hs : 1-s*z ≠ 0) :
    deriv (deriv (fun w : ℂ => w^(1-p.gamma)*h w)) z +
      drift f p s z*deriv (fun w : ℂ => w^(1-p.gamma)*h w) z +
      potential f p B s z*(z^(1-p.gamma)*h z) =
    z^(1-p.gamma) * (deriv (deriv h) z +
      drift f (exponentShiftParameters p) s z*deriv h z +
      potential f (exponentShiftParameters p) (exponentShiftAccessory f p B s) s z*h z) := by
  rw [cpow_mul_second_deriv h _ z hh hz, cpow_mul_deriv h _ z hh hz,
    exponentShift_drift, exponentShift_potential f p hb B s z
      (Complex.slitPlane_ne_zero hz) hz1 hs]
  have hz0 := Complex.slitPlane_ne_zero hz
  have hpow1 : z ^ ((1-p.gamma)-1) = z^(1-p.gamma)/z := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  have hpow2 : z ^ ((1-p.gamma)-2) = z^(1-p.gamma)/z^(2:ℕ) := by
    rw [Complex.cpow_sub _ _ hz0]
    norm_cast
  rw [hpow1, hpow2]
  field_simp
  ring

end Heun
#print axioms Heun.exponentShift_solution_identity
