import BanachRecurrence

noncomputable section
open scoped Topology
open Filter
namespace Heun

theorem decoded_base_endpoint (f : Family) (p : Parameters) (k : ℕ) :
    (∑' n, decode (encodePolynomial (basePolynomial f p k)) n) =
      (basePolynomial f p k).eval 1 := by
  calc
    _ = frobeniusSum f p (-D p k) 0 1 := by
      simp [frobeniusSum, decode_encodePolynomial, coeff_basePolynomial]
    _ = _ := frobeniusSum_basePolynomial f p k 1

/-- Every continuous bounded-sequence branch through the base polynomial has
nonzero value at endpoint one on a parameter neighborhood. -/
theorem decoded_endpoint_eventually_ne_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (x : ℂ → SeqSpace)
    (hx : ContinuousAt x 0) (hx0 : x 0=encodePolynomial (basePolynomial f p k)) :
    ∀ᶠ s in 𝓝 (0:ℂ), (∑' n, decode (x s) n) ≠ 0 := by
  let v := encodePolynomial (basePolynomial f p k)
  have hv : (∑' n, decode v n) ≠ 0 := by
    rw [decoded_base_endpoint]
    exact basePolynomial_eval_one_ne_zero f p hp k
  have hh : Tendsto (fun s => 2*‖x s-v‖) (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
    have ht := (hx.sub (continuousAt_const (y := v))).norm.const_mul (2:ℝ)
    simpa [hx0, v] using ht.tendsto
  have hn := hh.eventually_lt_const (norm_pos_iff.mpr hv)
  exact hn.mono fun s hs => decode_endpoint_ne_zero (x s) v hs

/-- A continuous Banach branch whose coordinates solve the literal recurrence
has zero actual endpoint connection coefficient near the base parameter. -/
theorem banach_branch_connection_zero (f : Family) (p : Parameters)
    (hp : Admissible f p) (k : ℕ) (x : ℂ → SeqSpace) (B : ℂ → ℂ)
    (hx : ContinuousAt x 0) (hx0 : x 0=encodePolynomial (basePolynomial f p k))
    (he : ∀ᶠ s in 𝓝 (0:ℂ), ∀ n, decode (x s) n=coefficient f p (B s) s n) :
    ∀ᶠ s in 𝓝 (0:ℂ), IsConnectionCoefficient f p (B s) s 0 := by
  have hval := decoded_endpoint_eventually_ne_zero f p hp k x hx hx0
  have hsmall : ∀ᶠ s in 𝓝 (0:ℂ), ‖s‖ ≤ (1/1000:ℝ) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1/1000)] with s hs
    exact (by simpa [Metric.mem_ball, dist_zero_right] using hs : ‖s‖ < (1/1000:ℝ)).le
  filter_upwards [hval, hsmall, he] with s hval hs he
  apply fast_frobenius_connection_zero f p hp (B s) s hs ‖x s‖ (norm_nonneg _)
  · intro n
    rw [← he n]
    exact decode_bound (x s) n
  · simpa only [frobeniusSum, one_pow, mul_one, ← he] using hval

end Heun
#print axioms Heun.banach_branch_connection_zero
