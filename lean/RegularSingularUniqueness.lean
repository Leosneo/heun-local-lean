import SingularGerm
import HeunProblem

noncomputable section
open scoped Topology
open Filter

namespace Heun

theorem pow_mul_second_euler {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (N : ℕ) :
    z ^ 2 * deriv (deriv (fun w : ℂ => w ^ N * g w)) z =
      z ^ N * ((N : ℂ) * ((N : ℂ) - 1) * g z +
        2 * (N : ℂ) * z * deriv g z + z ^ 2 * deriv (deriv g) z) := by
  have hd : deriv (fun w : ℂ => w ^ N * g w) =ᶠ[𝓝 z]
      (fun w => (N : ℂ) * w ^ (N-1) * g w + w ^ N * deriv g w) := by
    filter_upwards [hg.eventually_analyticAt] with w hgw
    simpa using (((hasDerivAt_id w).pow N).mul hgw.differentiableAt.hasDerivAt).deriv
  have hsecond := ((((hasDerivAt_id z).pow (N-1)).const_mul (N : ℂ)).mul
    hg.differentiableAt.hasDerivAt).add
    (((hasDerivAt_id z).pow N).mul hg.deriv.differentiableAt.hasDerivAt)
  change HasDerivAt (fun w : ℂ => (N : ℂ) * w ^ (N-1) * g w +
    w ^ N * deriv g w) _ z at hsecond
  have hsecond' : deriv (fun w : ℂ => (N : ℂ) * w ^ (N-1) * g w +
      w ^ N * deriv g w) z =
      ((N : ℂ) * ((N-1 : ℕ) : ℂ) * z ^ (N-1-1) * 1 * g z +
        (N : ℂ) * z ^ (N-1) * deriv g z) +
      ((N : ℂ) * z ^ (N-1) * 1 * deriv g z + z ^ N * deriv (deriv g) z) := by
    simpa [mul_assoc] using hsecond.deriv
  rw [hd.deriv_eq, hsecond']
  cases N with
  | zero => simp
  | succ N =>
    cases N with
    | zero => simp; ring
    | succ n =>
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

/-- Frobenius uniqueness for a regular-singular equation in normalized form.
No existence theorem or analytic dependence theorem is assumed. -/
theorem regular_singular_zero {y A B : ℂ → ℂ}
    (hy : AnalyticAt ℂ y 0) (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hgamma : ∀ n : ℕ, A 0 ≠ -(n : ℂ)) (hy0 : y 0 = 0)
    (hode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z * deriv (deriv y) z +
      A z * deriv y z + B z * y z = 0) :
    y =ᶠ[𝓝 (0 : ℂ)] 0 := by
  by_contra hne
  have htop : analyticOrderAt y 0 ≠ ⊤ :=
    fun h => hne (analyticOrderAt_eq_top.mp h)
  let N := analyticOrderNatAt y 0
  have hNorder : analyticOrderAt y 0 = (N : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt htop).symm
  have hN : N ≠ 0 := by
    intro hn
    have ho : analyticOrderAt y 0 = 0 := by simpa [hn] using hNorder
    exact (analyticOrderAt_eq_zero.mp ho).elim (fun h => h hy) (fun h => h hy0)
  obtain ⟨g, hg, hg0, hfactor⟩ := hy.analyticOrderAt_ne_top.mp htop
  have hfac : y =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ N * g z := by
    simpa [N, smul_eq_mul] using hfactor
  have hd := hfac.deriv
  have hdd := hd.deriv
  have he : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      (N : ℂ) * ((N : ℂ) - 1) * g z + 2 * (N : ℂ) * z * deriv g z +
        z ^ 2 * deriv (deriv g) z +
      A z * ((N : ℂ) * g z + z * deriv g z) + z * B z * g z = 0 := by
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds,
      hd.filter_mono nhdsWithin_le_nhds, hdd.filter_mono nhdsWithin_le_nhds,
      hode,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hfacz hdz hddz hodez hgz hz0
    have hsecond := pow_mul_second_euler hgz N
    have hfirst := Gcoy.SingularGerm.pow_mul_euler hgz.differentiableAt N
    rw [← hddz] at hsecond
    rw [← hdz] at hfirst
    apply (mul_eq_zero.mp (show z ^ N *
      ((N : ℂ) * ((N : ℂ) - 1) * g z + 2 * (N : ℂ) * z * deriv g z +
        z ^ 2 * deriv (deriv g) z +
      A z * ((N : ℂ) * g z + z * deriv g z) + z * B z * g z) = 0 from ?_)).resolve_left
      (pow_ne_zero N hz0)
    rw [hfacz] at hodez
    linear_combination z * hodez - hsecond - A z * hfirst
  have hcont : ContinuousAt (fun z : ℂ =>
      (N : ℂ) * ((N : ℂ) - 1) * g z + 2 * (N : ℂ) * z * deriv g z +
        z ^ 2 * deriv (deriv g) z +
      A z * ((N : ℂ) * g z + z * deriv g z) + z * B z * g z) 0 := by
    have hg' := hg.deriv.continuousAt
    have hg'' := hg.deriv.deriv.continuousAt
    have hgcont := hg.continuousAt
    have hAc := hA.continuousAt
    have hBc := hB.continuousAt
    fun_prop
  have hlim := hcont.tendsto.mono_left
    (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he0 : (N : ℂ) * ((N : ℂ) - 1) * g 0 + A 0 * ((N : ℂ) * g 0) = 0 := by
    have hz := tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' (he.mono fun z hz => hz.symm))
    simpa using hz
  have hNcast : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hres : (N : ℂ) - 1 + A 0 = 0 := by
    have hprod : (N : ℂ) * g 0 * ((N : ℂ) - 1 + A 0) = 0 := by
      linear_combination he0
    exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero hNcast hg0)
  apply hgamma (N - 1)
  have hcast : ((N-1 : ℕ) : ℂ) = (N : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  rw [hcast]
  linear_combination hres

theorem regular_singular_unique {y v A B : ℂ → ℂ}
    (hy : AnalyticAt ℂ y 0) (hv : AnalyticAt ℂ v 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (hgamma : ∀ n : ℕ, A 0 ≠ -(n : ℂ)) (h0 : y 0 = v 0)
    (hyode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z * deriv (deriv y) z +
      A z * deriv y z + B z * y z = 0)
    (hvode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z * deriv (deriv v) z +
      A z * deriv v z + B z * v z = 0) :
    y =ᶠ[𝓝 (0 : ℂ)] v := by
  have hd : deriv (y-v) =ᶠ[𝓝 (0 : ℂ)] deriv y - deriv v := by
    filter_upwards [hy.eventually_analyticAt, hv.eventually_analyticAt] with z hyz hvz
    exact deriv_sub hyz.differentiableAt hvz.differentiableAt
  have hdd := hd.deriv
  have hzero := regular_singular_zero (hy.sub hv) hA hB hgamma
    (by simpa using sub_eq_zero.mpr h0)
  have hode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z * deriv (deriv (y-v)) z +
      A z * deriv (y-v) z + B z * (y-v) z = 0 := by
    filter_upwards [hyode, hvode, hd.filter_mono nhdsWithin_le_nhds,
      hdd.filter_mono nhdsWithin_le_nhds,
      hy.deriv.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      hv.deriv.eventually_analyticAt.filter_mono nhdsWithin_le_nhds]
      with z hyz hvz hdz hddz hy'z hv'z
    rw [hddz, deriv_sub hy'z.differentiableAt hv'z.differentiableAt, hdz]
    simp only [Pi.sub_apply]
    linear_combination hyz - hvz
  have h := hzero hode
  filter_upwards [h] with z hz
  exact sub_eq_zero.mp hz

def zeroRegularA (f : Family) (p : Parameters) (s z : ℂ) : ℂ :=
  p.gamma + p.delta * z / (z - 1) + match f with
  | .heun => -(s * p.epsilon * z / (1 - s*z))
  | .confluent => -s*z
  | .reduced => 0

def zeroRegularB (f : Family) (p : Parameters) (B s z : ℂ) : ℂ :=
  match f with
  | .heun => (B-s*p.alpha*p.beta*z) / ((z-1)*(1-s*z))
  | .confluent => (B-s*p.alpha*z) / (z-1)
  | .reduced => (B-s*z) / (z-1)

theorem zeroRegularA_analytic (f : Family) (p : Parameters) (s : ℂ) :
    AnalyticAt ℂ (zeroRegularA f p s) 0 := by
  cases f <;> unfold zeroRegularA <;> fun_prop (disch := norm_num)

theorem zeroRegularB_analytic (f : Family) (p : Parameters) (B s : ℂ) :
    AnalyticAt ℂ (zeroRegularB f p B s) 0 := by
  cases f <;> unfold zeroRegularB <;> fun_prop (disch := norm_num)

@[simp] theorem zeroRegularA_zero (f : Family) (p : Parameters) (s : ℂ) :
    zeroRegularA f p s 0 = p.gamma := by cases f <;> simp [zeroRegularA]

theorem source_ODE_zero_normalized (f : Family) (p : Parameters) (B s : ℂ)
    {y : ℂ → ℂ}
    (hode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (deriv y) z +
      drift f p s z * deriv y z + potential f p B s z * y z = 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), z * deriv (deriv y) z +
      zeroRegularA f p s z * deriv y z + zeroRegularB f p B s z * y z = 0 := by
  have hz1 : ∀ᶠ z : ℂ in 𝓝 0, z - 1 ≠ 0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne (by norm_num)
  have hsz : ∀ᶠ z : ℂ in 𝓝 0, 1 - s*z ≠ 0 :=
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).eventually_ne (by norm_num)
  filter_upwards [hode, hz1.filter_mono nhdsWithin_le_nhds,
    hsz.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz1 hsz hz0
  have hzneq : z ≠ 0 := hz0
  have hA : zeroRegularA f p s z = z * drift f p s z := by
    cases f <;> simp only [zeroRegularA, drift] <;> field_simp [hzneq, hz1, hsz] <;> ring
  have hB : zeroRegularB f p B s z = z * potential f p B s z := by
    cases f <;> simp only [zeroRegularB, potential] <;> field_simp [hzneq, hz1, hsz] <;> ring
  rw [hA, hB]
  linear_combination z * hz

/-- Actual source-equation uniqueness, assuming only nonresonance of gamma. -/
theorem source_regular_zero_unique (f : Family) (p : Parameters) (B s : ℂ)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) {y v : ℂ → ℂ}
    (hy : AnalyticAt ℂ y 0) (hv : AnalyticAt ℂ v 0) (h0 : y 0 = v 0)
    (hyode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (deriv y) z +
      drift f p s z * deriv y z + potential f p B s z * y z = 0)
    (hvode : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (deriv v) z +
      drift f p s z * deriv v z + potential f p B s z * v z = 0) :
    y =ᶠ[𝓝 (0 : ℂ)] v :=
  regular_singular_unique hy hv (zeroRegularA_analytic f p s)
    (zeroRegularB_analytic f p B s) (by simpa using hgamma) h0
    (source_ODE_zero_normalized f p B s hyode)
    (source_ODE_zero_normalized f p B s hvode)

theorem source_regular_zero_unique_on (f : Family) (p : Parameters) (B s : ℂ)
    (hgamma : ∀ n : ℕ, p.gamma ≠ -(n : ℂ)) {y v : ℂ → ℂ}
    (hy : AnalyticOnNhd ℂ y zeroDisk) (hv : AnalyticOnNhd ℂ v zeroDisk)
    (hyode : SolvesOn f p B s y (zeroDisk \ {0}))
    (hvode : SolvesOn f p B s v (zeroDisk \ {0})) (h0 : y 0 = v 0) :
    Set.EqOn y v zeroDisk := by
  have hmem : (0 : ℂ) ∈ zeroDisk := by norm_num [zeroDisk, Metric.mem_ball]
  have hnear : ∀ᶠ z : ℂ in 𝓝 0, z ∈ zeroDisk :=
    Metric.isOpen_ball.mem_nhds hmem
  have hyo : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (deriv y) z +
      drift f p s z * deriv y z + potential f p B s z * y z = 0 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hn
    exact hyode.2 z ⟨hz, hn⟩
  have hvo : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (deriv v) z +
      drift f p s z * deriv v z + potential f p B s z * v z = 0 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hn
    exact hvode.2 z ⟨hz, hn⟩
  exact hy.eqOn_of_preconnected_of_eventuallyEq hv
    (convex_ball (0 : ℂ) (3/4 : ℝ)).isPreconnected hmem
    (source_regular_zero_unique f p B s hgamma (hy 0 hmem) (hv 0 hmem) h0 hyo hvo)

end Heun

#print axioms Heun.regular_singular_zero
#print axioms Heun.source_regular_zero_unique
#print axioms Heun.source_regular_zero_unique_on
