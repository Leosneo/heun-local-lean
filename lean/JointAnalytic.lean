import FrobeniusAnalytic
import CauchyBounds
import Mathlib.Analysis.Normed.Module.Connected
import AnalyticBridge
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Joint C¹ dependence suffices for the scalar analytic implicit branch.
No multivariate holomorphy theorem is postulated. -/
noncomputable section
open scoped Topology
open Filter
namespace Heun

/-- A complex C¹ implicit equation already gives an analytic scalar root. -/
theorem exists_analytic_implicit_branch_of_contDiffAt
    {f : ℂ × ℂ → ℂ} {u : ℂ × ℂ} (hf : ContDiffAt ℂ 1 f u)
    (hi : (fderiv ℂ f u ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g u.1 ∧ g u.1 = u.2 ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ g v.1 = v.2) := by
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hf.implicitFunction hn hi, ?_, hf.implicitFunction_apply_self hn hi,
    hf.eventually_apply_eq_iff_implicitFunction hn hi⟩
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hc := (hf.contDiffAt_implicitFunction hn hi).eventually (by simp)
  filter_upwards [hc] with z hz
  exact hz.differentiableAt (by simp)

/-- Uniform bounds on the derivative series imply genuine joint C¹ regularity. -/
theorem contDiffAt_tsum_of_uniform_fderiv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ℕ → E → ℂ} {U : Set E} {x : E} {bound : ℕ → ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hx : x ∈ U)
    (hg : ∀ n y, y ∈ U → ContDiffAt ℂ 1 (g n) y)
    (hbound : Summable bound)
    (hder : ∀ n y, y ∈ U → ‖fderiv ℂ (g n) y‖ ≤ bound n)
    (hsum : Summable (fun n => g n x)) :
    ContDiffAt ℂ 1 (fun y => ∑' n, g n y) x := by
  apply contDiffAt_one_iff.mpr
  refine ⟨fun y => ∑' n, fderiv ℂ (g n) y, U, hU.mem_nhds hx, ?_, ?_⟩
  · apply continuousOn_tsum _ hbound hder
    intro n y hy
    exact ((hg n y hy).continuousAt_fderiv (by simp)).continuousWithinAt
  · intro y hy
    exact hasFDerivAt_tsum_of_isPreconnected hbound hU hconn
      (fun n z hz => ((hg n z hz).differentiableAt (by simp)).hasFDerivAt)
      hder hx hsum hy

/-- This reduction isolates the remaining quantitative Cauchy estimate:
once the actual coefficient derivatives have a geometric bound, the
literal Frobenius sum is jointly C¹ in (s,B). -/
theorem frobeniusSum_contDiffAt_of_coefficient_fderiv_bound
    (f : Family) (p : Parameters) (z : ℂ) (U : Set (ℂ × ℂ))
    (hU : IsOpen U) (hconn : IsPreconnected U) (u : ℂ × ℂ) (hu : u ∈ U)
    (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hcoef : ∀ n, ‖coefficient f p u.2 u.1 n‖ ≤ C * (5 / 4 : ℝ) ^ n)
    (hder : ∀ n v, v ∈ U →
      ‖fderiv ℂ (fun w : ℂ × ℂ => coefficient f p w.2 w.1 n) v‖ ≤
        K * (5 / 4 : ℝ) ^ n)
    (hz : ‖z‖ < (4 / 5 : ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => frobeniusSum f p v.2 v.1 z) u := by
  have hq : (5 / 4 : ℝ) * ‖z‖ < 1 := by linarith
  apply contDiffAt_tsum_of_uniform_fderiv_bound hU hconn hu
    (bound := fun n => K * ((5 / 4 : ℝ) * ‖z‖) ^ n)
  · intro n v _
    exact ((coefficient_analytic f p n v).mul analyticAt_const).contDiffAt
  · exact (summable_geometric_of_lt_one (by positivity) hq).mul_left K
  · intro n v hv
    have hd := ((coefficient_analytic f p n v).differentiableAt.hasFDerivAt).mul_const (z ^ n)
    rw [hd.fderiv]
    calc
      _ ≤ ‖z ^ n‖ * ‖fderiv ℂ (fun w : ℂ × ℂ => coefficient f p w.2 w.1 n) v‖ := by
        rw [norm_smul]
      _ ≤ ‖z ^ n‖ * (K * (5 / 4 : ℝ) ^ n) := mul_le_mul_of_nonneg_left (hder n v hv) (norm_nonneg _)
      _ = K * ((5 / 4 : ℝ) * ‖z‖) ^ n := by rw [norm_pow, mul_pow]; ring
  · exact frobenius_summable f p u.2 u.1 z C hC hcoef hz

/-- Actual joint C¹ regularity, with all series derivative bounds discharged. -/
theorem frobeniusSum_contDiffAt (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B s z : ℂ)
    (hs : ‖s‖ < (1 / 100 : ℝ)) (hz : ‖z‖ < (4 / 5 : ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => frobeniusSum f p v.2 v.1 z) (s, B) := by
  obtain ⟨M₀, hM₀⟩ := exists_parameterBound p
  let M := M₀ + ‖B‖ + 1
  have hM : ParameterBound p M := by
    rcases hM₀ with ⟨h1, hγ, hδ, hε, hα, hβ⟩
    have hB0 := norm_nonneg B
    dsimp [M]
    unfold ParameterBound
    constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> linarith
  have hBM : ‖B‖ < M := by have := hM₀.1; dsimp [M]; linarith
  let ε := min (M - ‖B‖) (1 / 100 - ‖s‖) / 4
  have hmin : 0 < min (M - ‖B‖) (1 / 100 - ‖s‖) := lt_min (sub_pos.mpr hBM) (sub_pos.mpr hs)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεB : 2 * ε ≤ M - ‖B‖ := by
    have := min_le_left (M - ‖B‖) (1 / 100 - ‖s‖)
    dsimp [ε]; linarith [hmin]
  have hεs : 2 * ε ≤ 1 / 100 - ‖s‖ := by
    have := min_le_right (M - ‖B‖) (1 / 100 - ‖s‖)
    dsimp [ε]; linarith [hmin]
  obtain ⟨C, hC, hc⟩ := coefficient_geometric_bound f p hgamma hM
  apply frobeniusSum_contDiffAt_of_coefficient_fderiv_bound f p z
    (Metric.ball (s, B) ε) Metric.isOpen_ball Metric.isPreconnected_ball (s, B)
    (Metric.mem_ball_self hε) C (2 * (C / ε)) hC.le (by positivity)
    (hc B s hBM.le hs.le) _ hz
  intro n v hv
  have hvnorm : ‖v - (s, B)‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hv
  have hvB : ‖v.2 - B‖ < ε := lt_of_le_of_lt (norm_snd_le (v - (s, B))) hvnorm
  have hvs : ‖v.1 - s‖ < ε := lt_of_le_of_lt (norm_fst_le (v - (s, B))) hvnorm
  have hBtri : ‖v.2‖ ≤ ‖v.2 - B‖ + ‖B‖ := by simpa using norm_add_le (v.2 - B) B
  have hstri : ‖v.1‖ ≤ ‖v.1 - s‖ + ‖s‖ := by simpa using norm_add_le (v.1 - s) s
  exact coefficient_fderiv_bound f p v.2 v.1 M C ε hC.le hε hc
    (by linarith) (by linarith) n

/-- The same actual parameter regularity for any summably weighted
subsequence of the Frobenius coefficients, including z derivatives. -/
theorem coefficient_weightedSum_contDiffAt (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B s : ℂ)
    (hs : ‖s‖ < (1 / 100 : ℝ)) (index : ℕ → ℕ) (weight : ℕ → ℂ)
    (hweight : Summable (fun n => (5 / 4 : ℝ) ^ (index n) * ‖weight n‖)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ =>
      ∑' n, coefficient f p v.2 v.1 (index n) * weight n) (s, B) := by
  obtain ⟨M₀, hM₀⟩ := exists_parameterBound p
  let M := M₀ + ‖B‖ + 1
  have hM : ParameterBound p M := by
    rcases hM₀ with ⟨h1, hγ, hδ, hε, hα, hβ⟩
    have hB0 := norm_nonneg B
    dsimp [M]
    unfold ParameterBound
    constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> linarith
  have hBM : ‖B‖ < M := by have := hM₀.1; dsimp [M]; linarith
  let ε := min (M - ‖B‖) (1 / 100 - ‖s‖) / 4
  have hmin : 0 < min (M - ‖B‖) (1 / 100 - ‖s‖) :=
    lt_min (sub_pos.mpr hBM) (sub_pos.mpr hs)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεB : 2 * ε ≤ M - ‖B‖ := by
    have := min_le_left (M - ‖B‖) (1 / 100 - ‖s‖)
    dsimp [ε]; linarith
  have hεs : 2 * ε ≤ 1 / 100 - ‖s‖ := by
    have := min_le_right (M - ‖B‖) (1 / 100 - ‖s‖)
    dsimp [ε]; linarith
  obtain ⟨C, hC, hc⟩ := coefficient_geometric_bound f p hgamma hM
  let K := 2 * (C / ε)
  have hder : ∀ n v, v ∈ Metric.ball (s, B) ε →
      ‖fderiv ℂ (fun w : ℂ × ℂ => coefficient f p w.2 w.1 n) v‖ ≤ K * (5 / 4 : ℝ) ^ n := by
    intro n v hv
    have hvnorm : ‖v - (s, B)‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using hv
    have hvB : ‖v.2 - B‖ < ε := lt_of_le_of_lt (norm_snd_le (v - (s, B))) hvnorm
    have hvs : ‖v.1 - s‖ < ε := lt_of_le_of_lt (norm_fst_le (v - (s, B))) hvnorm
    have hBtri : ‖v.2‖ ≤ ‖v.2 - B‖ + ‖B‖ := by simpa using norm_add_le (v.2 - B) B
    have hstri : ‖v.1‖ ≤ ‖v.1 - s‖ + ‖s‖ := by simpa using norm_add_le (v.1 - s) s
    exact coefficient_fderiv_bound f p v.2 v.1 M C ε hC.le hε hc (by linarith) (by linarith) n
  apply contDiffAt_tsum_of_uniform_fderiv_bound Metric.isOpen_ball Metric.isPreconnected_ball
    (Metric.mem_ball_self hε) (bound := fun n => K * ((5 / 4 : ℝ) ^ (index n) * ‖weight n‖))
  · intro n v _
    exact ((coefficient_analytic f p (index n) v).mul analyticAt_const).contDiffAt
  · exact hweight.mul_left K
  · intro n v hv
    have hd := ((coefficient_analytic f p (index n) v).differentiableAt.hasFDerivAt).mul_const (weight n)
    rw [hd.fderiv, norm_smul]
    calc
      _ ≤ ‖weight n‖ * (K * (5 / 4 : ℝ) ^ (index n)) :=
        mul_le_mul_of_nonneg_left (hder (index n) v hv) (norm_nonneg _)
      _ = _ := by ring
  · apply Summable.of_norm_bounded (hweight.mul_left C)
    intro n
    rw [norm_mul]
    calc
      _ ≤ (C * (5 / 4 : ℝ) ^ (index n)) * ‖weight n‖ :=
        mul_le_mul_of_nonneg_right (hc B s hBM.le hs.le (index n)) (norm_nonneg _)
      _ = _ := by ring

theorem frobenius_deriv_eq_shifted (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B s z : ℂ)
    (hs : ‖s‖ < (1 / 100 : ℝ)) (hz : ‖z‖ < (4 / 5 : ℝ)) :
    deriv (frobeniusSum f p B s) z =
      ∑' n : ℕ, coefficient f p B s (n + 1) * ((n + 1 : ℂ) * z ^ n) := by
  obtain ⟨M₀, hM₀⟩ := exists_parameterBound p
  let M := M₀ + ‖B‖ + 1
  have hM : ParameterBound p M := by
    rcases hM₀ with ⟨h1, hγ, hδ, hε, hα, hβ⟩
    have hB0 := norm_nonneg B
    dsimp [M]
    unfold ParameterBound
    constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> linarith
  obtain ⟨C, hC, hc⟩ := coefficient_geometric_bound f p hgamma hM
  have hB : ‖B‖ ≤ M := by have := hM₀.1; dsimp [M]; linarith
  have he := (frobenius_hasSum_deriv f p B s z C hC.le (hc B s hB hs.le) hz).tsum_eq.symm
  exact he.trans (tsum_congr (fun n => by ring))

/-- Actual joint parameter regularity of the z-derivative used in the
Wronskian connection formula. -/
theorem frobeniusDeriv_contDiffAt (f : Family) (p : Parameters)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) (B s z : ℂ)
    (hs : ‖s‖ < (1 / 100 : ℝ)) (hz : ‖z‖ < (4 / 5 : ℝ)) :
    ContDiffAt ℂ 1 (fun v : ℂ × ℂ => deriv (frobeniusSum f p v.2 v.1) z) (s, B) := by
  let q := (5 / 4 : ℝ) * ‖z‖
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; dsimp [q]; linarith
  have hn := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have hg := summable_geometric_of_norm_lt_one hq
  have hw : Summable (fun n : ℕ => (5 / 4 : ℝ) ^ (n + 1) * ‖(n + 1 : ℂ) * z ^ n‖) := by
    have ht := (hn.add hg).mul_left (5 / 4 : ℝ)
    convert ht using 1
    ext n
    have hnorm : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by simpa using Complex.norm_natCast (n + 1)
    rw [norm_mul, hnorm, norm_pow]
    dsimp [q]
    rw [pow_succ, mul_pow]
    ring
  have hc := coefficient_weightedSum_contDiffAt f p hgamma B s hs
    (fun n => n + 1) (fun n => (n + 1 : ℂ) * z ^ n) hw
  apply hc.congr_of_eventuallyEq
  have he : ∀ᶠ v : ℂ × ℂ in 𝓝 (s, B), ‖v.1‖ < (1 / 100 : ℝ) :=
    (continuousAt_fst.norm).eventually_lt_const hs
  filter_upwards [he] with v hv
  exact frobenius_deriv_eq_shifted f p hgamma v.2 v.1 z hv hz

#print axioms frobeniusDeriv_contDiffAt
#print axioms frobeniusSum_contDiffAt
#print axioms exists_analytic_implicit_branch_of_contDiffAt
end Heun
