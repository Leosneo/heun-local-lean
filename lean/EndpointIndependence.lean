import SingularSolution
import SingularGerm
import ODEUniqueness
import Mathlib.Analysis.Complex.Convex

noncomputable section
open scoped Topology
open Filter
namespace Heun

def endpointHalfDisk : Set ℂ := oneDisk ∩ {z | z.re < 1}
def originHalfDisk : Set ℂ := zeroDisk ∩ {z | 0 < z.re}

theorem endpointHalfDisk_preconnected : IsPreconnected endpointHalfDisk :=
  ((convex_ball (1:ℂ) (3/4:ℝ)).inter (convex_halfSpace_re_lt 1)).isPreconnected

theorem endpointHalfDisk_midpoint : (1/2:ℂ) ∈ endpointHalfDisk := by
  norm_num [endpointHalfDisk, oneDisk, Metric.mem_ball, dist_eq_norm]

theorem originHalfDisk_open : IsOpen originHalfDisk :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem originHalfDisk_slit : originHalfDisk ⊆ Complex.slitPlane := by
  intro z hz
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hz.2)

theorem originHalfDisk_zero_neBot : NeBot (𝓝[originHalfDisk] (0:ℂ)) := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  rw [Metric.mem_closure_iff]
  intro e he
  let a : ℝ := min (e/2) (1/4)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have hal : a < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have har : a < (3/4:ℝ) := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨(a:ℂ), ⟨?_, ?_⟩, ?_⟩
  · simpa [zeroDisk, Metric.mem_ball, dist_zero_right, Complex.norm_real, abs_of_pos ha] using har
  · simpa using ha
  · simpa [dist_eq_norm, Complex.norm_real, abs_of_pos ha] using hal

theorem origin_to_endpoint_half {z : ℂ} (hz : z ∈ originHalfDisk) :
    1-z ∈ endpointHalfDisk := by
  constructor
  · simpa [zeroDisk, oneDisk, Metric.mem_ball, dist_eq_norm] using hz.1
  · simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
    have hr : 0 < z.re := hz.2
    linarith

theorem singular_analytic_half (p : Parameters) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h oneDisk) :
    AnalyticOnNhd ℂ (singularSolution p h) endpointHalfDisk := by
  intro z hz
  have hs : 1-z ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.one_re]
    have hr : z.re < 1 := hz.2
    linarith
  exact ((analyticAt_const.sub analyticAt_id).cpow analyticAt_const hs).mul (hh z hz.1)

/-- The normalized regular and noninteger singular endpoint functions are
linearly independent as actual analytic germs at the midpoint. The proof
continues through a connected half-disk that really approaches the endpoint. -/
theorem endpoint_germs_independent (p : Parameters)
    (hdelta : ∀ m : ℤ, p.delta ≠ (m:ℂ)) (u h : ℂ → ℂ)
    (hu : AnalyticOnNhd ℂ u oneDisk) (hu1 : u 1 = 1)
    (hh : AnalyticOnNhd ℂ h oneDisk) (hh1 : h 1 = 1)
    (a b : ℂ)
    (heq : ∀ᶠ z in 𝓝 (1/2:ℂ), a*u z + b*singularSolution p h z = 0) :
    a = 0 ∧ b = 0 := by
  have h1mem : (1:ℂ) ∈ oneDisk := by norm_num [oneDisk, Metric.mem_ball]
  have hb : b = 0 := by
    by_contra hbn
    have hev : singularSolution p h =ᶠ[𝓝 (1/2:ℂ)] (fun z => (-a/b)*u z) := by
      filter_upwards [heq] with z hz
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hbn).mpr
      linear_combination hz
    have hscalar : AnalyticOnNhd ℂ (fun z => (-a/b)*u z) endpointHalfDisk :=
      fun z hz => analyticAt_const.mul (hu z hz.1)
    have heU := (singular_analytic_half p h hh).eqOn_of_preconnected_of_eventuallyEq
      hscalar endpointHalfDisk_preconnected endpointHalfDisk_midpoint hev
    letI := originHalfDisk_zero_neBot
    have ht : AnalyticAt ℂ (fun w : ℂ => 1-w) 0 := analyticAt_const.sub analyticAt_id
    have hhu : AnalyticAt ℂ (fun w => h (1-w)) 0 :=
      (hh 1 h1mem).comp_of_eq ht (by simp)
    have hua : AnalyticAt ℂ (fun w => (-a/b)*u (1-w)) 0 :=
      analyticAt_const.mul ((hu 1 h1mem).comp_of_eq ht (by simp))
    have hex : ∀ n : ℕ, (1-p.delta:ℂ) ≠ (n:ℂ) := by
      intro n hn
      apply hdelta (1-(n:ℤ))
      push_cast
      linear_combination -hn
    apply Gcoy.SingularGerm.cpow_mul_not_regularGerms originHalfDisk originHalfDisk_open
      originHalfDisk_slit (1-p.delta) hex (fun w => h (1-w)) hhu (by simp [hh1])
    refine ⟨(fun w => (-a/b)*u (1-w)), hua, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    simpa [singularSolution] using heU (origin_to_endpoint_half hw)
  refine ⟨?_, hb⟩
  have haz : (fun z => a*u z) =ᶠ[𝓝 (1/2:ℂ)] (fun _ => 0) := by
    filter_upwards [heq] with z hz
    simpa [hb] using hz
  have hau : AnalyticOnNhd ℂ (fun z => a*u z) oneDisk :=
    fun z hz => analyticAt_const.mul (hu z hz)
  have heU := hau.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    (convex_ball (1:ℂ) (3/4:ℝ)).isPreconnected endpointHalfDisk_midpoint.1 haz
  simpa [hu1] using heU h1mem

#print axioms endpoint_germs_independent

/-- Ordinary-point ODE uniqueness upgrades endpoint germ independence to
nonvanishing of the actual midpoint Wronskian. -/
theorem endpoint_wronskian_ne_zero (p : Parameters)
    (hdelta : ∀ m : ℤ, p.delta ≠ (m:ℂ)) (u h a b : ℂ → ℂ)
    (hu : AnalyticOnNhd ℂ u oneDisk) (hu1 : u 1 = 1)
    (hh : AnalyticOnNhd ℂ h oneDisk) (hh1 : h 1 = 1)
    (ha : AnalyticAt ℂ a (1/2:ℂ)) (hb : AnalyticAt ℂ b (1/2:ℂ))
    (huode : ∀ᶠ z in 𝓝 (1/2:ℂ), deriv (deriv u) z + a z*deriv u z+b z*u z=0)
    (hvode : ∀ᶠ z in 𝓝 (1/2:ℂ), deriv (deriv (singularSolution p h)) z +
      a z*deriv (singularSolution p h) z+b z*singularSolution p h z=0) :
    u (1/2) * deriv (singularSolution p h) (1/2) -
      deriv u (1/2) * singularSolution p h (1/2) ≠ 0 := by
  let c : ℂ := 1/2
  let v := singularSolution p h
  have huat : AnalyticAt ℂ u c := hu c endpointHalfDisk_midpoint.1
  have hvat : AnalyticAt ℂ v c := singular_analytic_half p h hh c endpointHalfDisk_midpoint
  have hzero : ∀ A B : ℂ, A*u c+B*v c=0 → A*deriv u c+B*deriv v c=0 → A=0 ∧ B=0 := by
    intro A B hval hder
    have hlin := analytic_second_order_linear_combination huat hvat A B huode hvode
    have hw := analytic_second_order_zero
      ((analyticAt_const.mul huat).add (analyticAt_const.mul hvat)) ha hb hval
      (by change deriv (fun z => A*u z+B*v z) c = 0
          rw [hlin.1.self_of_nhds]
          exact hder) hlin.2
    exact endpoint_germs_independent p hdelta u h hu hu1 hh hh1 A B hw
  intro hW
  change u c*deriv v c - deriv u c*v c=0 at hW
  by_cases hu0 : u c = 0
  · have hud : deriv u c ≠ 0 := by
      intro hd
      have hh := hzero 1 0 (by simp [hu0]) (by simp [hd])
      norm_num at hh
    have hv0 : v c = 0 := by
      rw [hu0, zero_mul, zero_sub, neg_eq_zero] at hW
      exact (mul_eq_zero.mp hW).resolve_left hud
    have he := hzero (-deriv v c) (deriv u c) (by simp [hu0, hv0]) (by ring)
    exact hud he.2
  · have he := hzero (-v c) (u c) (by ring) (by linear_combination hW)
    exact hu0 he.2

#print axioms endpoint_wronskian_ne_zero

theorem ordinary_midpoint_coefficients (f : Family) (p : Parameters) (B s : ℂ)
    (hs : ‖s‖ ≤ (1/1000:ℝ)) :
    AnalyticAt ℂ (drift f p s) (1/2:ℂ) ∧
      AnalyticAt ℂ (potential f p B s) (1/2:ℂ) := by
  have hsm : 1-s*(1/2:ℂ) ≠ 0 := by
    intro h
    have he : s = 2 := by linear_combination -2*h
    norm_num [he] at hs
  constructor <;> cases f <;>
    change AnalyticAt ℂ (fun z => _) _ <;>
    dsimp only [drift, potential] <;>
    fun_prop (disch := first | assumption | norm_num [mul_ne_zero, hsm])

theorem overlap_midpoint : (1/2:ℂ) ∈ overlap := by
  norm_num [overlap, zeroDisk, oneDisk, Metric.mem_ball, dist_eq_norm]

theorem overlap_open : IsOpen overlap := Metric.isOpen_ball.inter Metric.isOpen_ball

theorem actual_endpoint_wronskian_ne_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ)) :
    regularOne f p B s (1/2) *
      deriv (singularSolution p (singularFactor f p B s)) (1/2) -
      deriv (regularOne f p B s) (1/2) *
        singularSolution p (singularFactor f p B s) (1/2) ≠ 0 := by
  have hd : ∀ n : ℕ, p.delta ≠ -(n:ℂ) := by
    intro n
    simpa using hp.2.1 (-(n:ℤ))
  obtain ⟨hu, hu1, huode⟩ := regularOne_solution f p hd hp.2.2.2 B s hs
  obtain ⟨hh, hh1, hvode⟩ := singularFactor_solution f p hp.2.1 hp.2.2.2 B s hs
  obtain ⟨ha, hb⟩ := ordinary_midpoint_coefficients f p B s hs
  apply endpoint_wronskian_ne_zero p hp.2.1 (regularOne f p B s)
    (singularFactor f p B s) (drift f p s) (potential f p B s) hu hu1 hh hh1 ha hb
  · filter_upwards [overlap_open.mem_nhds overlap_midpoint] with z hz
    apply huode.2 z
    refine ⟨hz.2, ?_⟩
    have hzn : ‖z‖ < (3/4:ℝ) := by
      simpa [zeroDisk, Metric.mem_ball, dist_zero_right] using hz.1
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hzn
    simpa using hz1
  · filter_upwards [overlap_open.mem_nhds overlap_midpoint] with z hz
    exact hvode.2 z hz

#print axioms actual_endpoint_wronskian_ne_zero

/-- The normalized Frobenius bases give an actual connection identity for every
accessory parameter, with no connection-existence hypothesis. -/
theorem actual_connection_exists (f : Family) (p : Parameters)
    (hp : Admissible f p) (B s : ℂ) (hs : ‖s‖ ≤ (1/1000:ℝ)) :
    ∃ d₂ : ℂ, IsConnectionCoefficient f p B s d₂ := by
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
  obtain ⟨d₁, d₂, heq⟩ := analytic_second_order_span
    (fun z hz => hy z hz.1) (fun z hz => hu z hz.2) hvode.1
    hconn overlap_midpoint ha hb hyO huO hvO
    (actual_endpoint_wronskian_ne_zero f p hp B s hs)
  exact ⟨d₂, frobeniusSum f p B s, regularOne f p B s,
    singularFactor f p B s, d₁, hy, hy0, hyode, hu, hu1, huode,
    hh, hh1, hvode, heq⟩

#print axioms actual_connection_exists
end Heun
