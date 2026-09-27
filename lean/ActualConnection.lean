import EndpointIndependence
import ConnectionUniqueness
import BaseConnection

noncomputable section
open Topology Filter
namespace Heun

theorem analytic_second_order_span_explicit {y u v a b : ℂ → ℂ} {c : ℂ} {U : Set ℂ}
    (hy : AnalyticOnNhd ℂ y U) (hu : AnalyticOnNhd ℂ u U)
    (hv : AnalyticOnNhd ℂ v U) (hU : IsPreconnected U) (hc : c ∈ U)
    (ha : AnalyticAt ℂ a c) (hb : AnalyticAt ℂ b c)
    (hyode : ∀ᶠ z in 𝓝 c, deriv (deriv y) z + a z * deriv y z + b z * y z = 0)
    (huode : ∀ᶠ z in 𝓝 c, deriv (deriv u) z + a z * deriv u z + b z * u z = 0)
    (hvode : ∀ᶠ z in 𝓝 c, deriv (deriv v) z + a z * deriv v z + b z * v z = 0)
    (hW : u c * deriv v c - deriv u c * v c ≠ 0) :
    Set.EqOn y (fun z =>
      ((y c * deriv v c - deriv y c * v c) / (u c * deriv v c - deriv u c * v c)) * u z +
      ((u c * deriv y c - deriv u c * y c) / (u c * deriv v c - deriv u c * v c)) * v z) U := by
  let W := u c * deriv v c - deriv u c * v c
  let d₁ := (y c * deriv v c - deriv y c * v c) / W
  let d₂ := (u c * deriv y c - deriv u c * y c) / W
  have hd := analytic_second_order_linear_combination (hu c hc) (hv c hc)
    d₁ d₂ huode hvode
  have hw : AnalyticOnNhd ℂ (fun z => d₁ * u z + d₂ * v z) U :=
    fun z hz => (analyticAt_const.mul (hu z hz)).add
      (analyticAt_const.mul (hv z hz))
  change Set.EqOn y (fun z => d₁ * u z + d₂ * v z) U
  apply analytic_second_order_unique_on hy hw hU hc ha hb _ _ hyode hd.2
  · change y c = d₁ * u c + d₂ * v c
    dsimp [d₁, d₂]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff (show W ≠ 0 from hW)).mpr
    dsimp [W]
    ring
  · change deriv y c = deriv (fun z => d₁ * u z + d₂ * v z) c
    rw [hd.1.self_of_nhds]
    dsimp [d₁, d₂]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (eq_div_iff (show W ≠ 0 from hW)).mpr
    dsimp [W]
    ring

#print axioms analytic_second_order_span_explicit

/-- The endpoint-basis Wronskian at the ordinary midpoint. -/
def actualWronskian (f : Family) (p : Parameters) (B s : ℂ) : ℂ :=
  regularOne f p B s (1/2) *
    deriv (singularSolution p (singularFactor f p B s)) (1/2) -
  deriv (regularOne f p B s) (1/2) *
    singularSolution p (singularFactor f p B s) (1/2)

/-- Literal Cramer formula for the singular connection coefficient. -/
def actualConnection (f : Family) (p : Parameters) (B s : ℂ) : ℂ :=
  (regularOne f p B s (1/2) * deriv (frobeniusSum f p B s) (1/2) -
    deriv (regularOne f p B s) (1/2) * frobeniusSum f p B s (1/2)) /
    actualWronskian f p B s

theorem actualConnection_spec (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ)) :
    IsConnectionCoefficient f p B s (actualConnection f p B s) := by
  have hd : ∀ n : ℕ, p.delta ≠ -(n:ℂ) := by
    intro n
    simpa using hp.2.1 (-(n:ℤ))
  obtain ⟨hy, hy0, hyode⟩ := frobeniusSum_regular_zero_solution f p hp B s (by linarith)
  obtain ⟨hu, hu1, huode⟩ := regularOne_solution f p hd hp.2.2.2 B s hs
  obtain ⟨hh, hh1, hvode⟩ := singularFactor_solution f p hp.2.1 hp.2.2.2 B s hs
  obtain ⟨ha, hb⟩ := ordinary_midpoint_coefficients f p B s hs
  have hyO : ∀ᶠ z in 𝓝 (1/2:ℂ),
      deriv (deriv (frobeniusSum f p B s)) z +
      drift f p s z * deriv (frobeniusSum f p B s) z +
      potential f p B s z * frobeniusSum f p B s z = 0 := by
    filter_upwards [overlap_open.mem_nhds overlap_midpoint] with z hz
    apply hyode.2 z
    refine ⟨hz.1, ?_⟩
    have hzn : ‖z-1‖ < (3/4:ℝ) := by
      simpa [oneDisk, Metric.mem_ball, dist_eq_norm] using hz.2
    have hz0 : z ≠ 0 := by intro he; norm_num [he] at hzn
    simpa using hz0
  have huO : ∀ᶠ z in 𝓝 (1/2:ℂ),
      deriv (deriv (regularOne f p B s)) z +
      drift f p s z * deriv (regularOne f p B s) z +
      potential f p B s z * regularOne f p B s z = 0 := by
    filter_upwards [overlap_open.mem_nhds overlap_midpoint] with z hz
    apply huode.2 z
    refine ⟨hz.2, ?_⟩
    have hzn : ‖z‖ < (3/4:ℝ) := by
      simpa [zeroDisk, Metric.mem_ball, dist_zero_right] using hz.1
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hzn
    simpa using hz1
  have hvO : ∀ᶠ z in 𝓝 (1/2:ℂ),
      deriv (deriv (singularSolution p (singularFactor f p B s))) z +
      drift f p s z * deriv (singularSolution p (singularFactor f p B s)) z +
      potential f p B s z * singularSolution p (singularFactor f p B s) z = 0 := by
    filter_upwards [overlap_open.mem_nhds overlap_midpoint] with z hz
    exact hvode.2 z hz
  have hconn : IsPreconnected overlap :=
    ((convex_ball (0:ℂ) (3/4:ℝ)).inter (convex_ball (1:ℂ) (3/4:ℝ))).isPreconnected
  have heq := analytic_second_order_span_explicit
    (fun z hz => hy z hz.1) (fun z hz => hu z hz.2) hvode.1
    hconn overlap_midpoint ha hb hyO huO hvO
    (actual_endpoint_wronskian_ne_zero f p hp B s hs)
  exact ⟨frobeniusSum f p B s, regularOne f p B s,
    singularFactor f p B s, _, hy, hy0, hyode, hu, hu1, huode,
    hh, hh1, hvode, heq⟩

#print axioms actualConnection_spec

theorem actualConnection_base (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) : actualConnection f p (-D p k) 0 = 0 :=
  isConnectionCoefficient_unique f p hp (-D p k) 0 _ 0
    (actualConnection_spec f p hp (-D p k) 0 (by norm_num))
    (base_IsConnectionCoefficient f p hp k)

#print axioms actualConnection_base
end Heun
