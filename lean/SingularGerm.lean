import AnalyticBridge
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open scoped Topology
open Filter

namespace Gcoy.SingularGerm

theorem pow_mul_euler {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (n : ℕ) :
    z * deriv (fun w : ℂ => w ^ n * g w) z =
      z ^ n * ((n : ℂ) * g z + z * deriv g z) := by
  have h := ((hasDerivAt_id z).pow n).mul hg.hasDerivAt
  have hd : deriv (fun w : ℂ => w ^ n * g w) z =
      (n : ℂ) * z ^ (n - 1) * 1 * g z + z ^ n * deriv g z := h.deriv
  rw [hd]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
    ring

/-- A nonzero holomorphic Euler eigen-germ has a nonnegative integer exponent.
This is a vanishing-order argument, not a hypothesis about complex powers. -/
theorem analytic_euler_exponent_nat {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hne : ¬ (f =ᶠ[𝓝 (0 : ℂ)] 0))
    (heuler : ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv f z = a * f z) :
    ∃ n : ℕ, a = (n : ℂ) := by
  have ho : analyticOrderAt f 0 ≠ ⊤ := by
    intro htop
    exact hne (analyticOrderAt_eq_top.mp htop)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp ho
  let n := analyticOrderNatAt f 0
  have hfactor : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    simpa [n, smul_eq_mul] using hfg
  have hder := hfactor.deriv
  have he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (n : ℂ) * g z + z * deriv g z = a * g z := by
    filter_upwards [heuler.filter_mono nhdsWithin_le_nhds,
      hfactor.filter_mono nhdsWithin_le_nhds,
      hder.filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hfz hdz hgz hzne
    have hz0 : z ≠ 0 := hzne
    rw [hdz, hfz, pow_mul_euler hgz.differentiableAt n] at hz
    apply mul_left_cancel₀ (pow_ne_zero n hz0)
    calc
      z ^ n * ((n : ℂ) * g z + z * deriv g z) = a * (z ^ n * g z) := hz
      _ = z ^ n * (a * g z) := by ring
  have hcont : ContinuousAt (fun z : ℂ => (n : ℂ) * g z + z * deriv g z) 0 :=
    (continuousAt_const.mul hg.continuousAt).add
      (continuousAt_id.mul hg.deriv.continuousAt)
  have hlim := hcont.tendsto.mono_left
    (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ) from nhdsWithin_le_nhds)
  have hlim' := ((continuousAt_const (y := a)).mul hg.continuousAt).tendsto.mono_left
    (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ) from nhdsWithin_le_nhds)
  have he0 : (n : ℂ) * g 0 = a * g 0 := by
    have he' : (fun z : ℂ => (n : ℂ) * g z + z * deriv g z) =ᶠ[𝓝[≠] 0]
        (fun z => a * g z) := he
    simpa using tendsto_nhds_unique hlim (hlim'.congr' he'.symm)
  exact ⟨n, (mul_right_cancel₀ hg0 he0).symm⟩

/-- Noninteger exponents rule out a nonzero analytic Euler eigen-germ. -/
theorem analytic_euler_eq_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f 0) (ha : ∀ n : ℕ, a ≠ (n : ℂ))
    (heuler : ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv f z = a * f z) :
    f =ᶠ[𝓝 (0 : ℂ)] 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := analytic_euler_exponent_nat hf hne heuler
  exact ha n hn

/-- The principal complex power satisfies the concrete Euler equation on its
actual holomorphic domain, the slit plane. -/
theorem cpow_euler (a z : ℂ) (hz : z ∈ Complex.slitPlane) :
    z * deriv (fun w : ℂ => w ^ a) z = a * z ^ a := by
  rw [Complex.deriv_cpow_const hz, Complex.cpow_sub _ _ (Complex.slitPlane_ne_zero hz),
    Complex.cpow_one]
  field_simp [Complex.slitPlane_ne_zero hz]

/-- The principal noninteger power has no analytic extension across zero from
any open approach region in the slit plane that actually accumulates at zero. -/
theorem cpow_not_regularGerms (S : Set ℂ) (hS : IsOpen S)
    (hsub : S ⊆ Complex.slitPlane) [NeBot (𝓝[S] (0 : ℂ))]
    (a : ℂ) (ha : ∀ n : ℕ, a ≠ (n : ℂ)) :
    (fun z : ℂ => z ^ a) ∉ Gcoy.AnalyticBridge.regularGerms S 0 := by
  rintro ⟨g, hg, heq⟩
  have hn : ¬ (g =ᶠ[𝓝 (0 : ℂ)] 0) := by
    intro hz
    have hfalse : ∀ᶠ z in 𝓝[S] (0 : ℂ), False := by
      filter_upwards [heq, hz.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with z he hz hzs
      have hzn : z ≠ 0 := Complex.slitPlane_ne_zero (hsub hzs)
      exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hzn)) (he.trans hz)
    obtain ⟨z, hz⟩ := hfalse.exists
    exact hz
  have heS : ∀ᶠ z in 𝓝[S] (0 : ℂ), z * deriv g z = a * g z := by
    filter_upwards [heq, eventually_eventually_nhdsWithin.mpr heq,
      self_mem_nhdsWithin] with z he hlocal hzs
    have hlocal' : (fun w : ℂ => w ^ a) =ᶠ[𝓝 z] g := by
      simpa only [hS.nhdsWithin_eq hzs] using hlocal
    rw [← hlocal'.deriv_eq, ← he]
    exact cpow_euler a z (hsub hzs)
  have hle : 𝓝[S] (0 : ℂ) ≤ 𝓝[≠] (0 : ℂ) := by
    apply nhdsWithin_mono
    intro z hz
    exact Complex.slitPlane_ne_zero (hsub hz)
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv g z = a * g z :=
    ((analyticAt_id.mul hg.deriv).frequently_eq_iff_eventually_eq
      (analyticAt_const.mul hg)).mp (heS.frequently.filter_mono hle)
  obtain ⟨n, hn⟩ := analytic_euler_exponent_nat hg hn he
  exact ha n hn

/-- Multiplication by a holomorphic unit cannot remove the branch obstruction. -/
theorem cpow_mul_not_regularGerms (S : Set ℂ) (hS : IsOpen S)
    (hsub : S ⊆ Complex.slitPlane) [NeBot (𝓝[S] (0 : ℂ))]
    (a : ℂ) (ha : ∀ n : ℕ, a ≠ (n : ℂ))
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0) :
    (fun z : ℂ => z ^ a * h z) ∉ Gcoy.AnalyticBridge.regularGerms S 0 := by
  rintro ⟨g, hg, heq⟩
  apply cpow_not_regularGerms S hS hsub a ha
  refine ⟨(fun z => g z / h z), hg.div hh hh0, ?_⟩
  have hhn : ∀ᶠ z in 𝓝 (0 : ℂ), h z ≠ 0 := hh.continuousAt.eventually_ne hh0
  filter_upwards [heq, hhn.filter_mono nhdsWithin_le_nhds] with z hz hzne
  exact (eq_div_iff hzne).mpr hz

theorem slitPlane_zero_neBot : NeBot (𝓝[Complex.slitPlane] (0 : ℂ)) := by
  apply mem_closure_iff_nhdsWithin_neBot.mp
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((ε / 2 : ℝ) : ℂ), Complex.ofReal_mem_slitPlane.mpr (by positivity), ?_⟩
  simpa [dist_eq_norm, Complex.norm_real, abs_of_pos hε]
    using (show ε / 2 < ε by linarith)

/-- The slit approach to one reaches one; unlike a fixed overlap of small
endpoint disks, this is a legitimate domain for singular-germ arguments. -/
def oneSlit : Set ℂ := {z | 1 - z ∈ Complex.slitPlane}

theorem oneSlit_isOpen : IsOpen oneSlit :=
  Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)

theorem oneSlit_one_neBot : NeBot (𝓝[oneSlit] (1 : ℂ)) := by
  letI := slitPlane_zero_neBot
  have ht : Tendsto (fun w : ℂ => 1 - w) (𝓝[Complex.slitPlane] 0)
      (𝓝[oneSlit] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun w : ℂ => 1 - w) 0 :=
        continuousAt_const.sub continuousAt_id
      simpa using hc.tendsto.mono_left
        (show 𝓝[Complex.slitPlane] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simpa [oneSlit] using hw
  exact ht.neBot

theorem singular_not_regularGerms (δ : ℂ)
    (hδ : ∀ m : ℤ, δ ≠ (m : ℂ)) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 1) (hh1 : h 1 = 1) :
    (fun z : ℂ => (1 - z) ^ (1 - δ) * h z) ∉
      Gcoy.AnalyticBridge.regularGerms oneSlit 1 := by
  rintro ⟨g, hg, heq⟩
  letI := slitPlane_zero_neBot
  have htrans : AnalyticAt ℂ (fun w : ℂ => 1 - w) 0 :=
    analyticAt_const.sub analyticAt_id
  have hhc : AnalyticAt ℂ (fun w : ℂ => h (1 - w)) 0 := by
    exact hh.comp_of_eq htrans (by simp)
  have hgc : AnalyticAt ℂ (fun w : ℂ => g (1 - w)) 0 := by
    exact hg.comp_of_eq htrans (by simp)
  have ha : ∀ n : ℕ, (1 - δ : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hδ (1 - (n : ℤ))
    push_cast
    linear_combination -hn
  apply cpow_mul_not_regularGerms Complex.slitPlane Complex.isOpen_slitPlane
    (fun _ hz => hz) (1 - δ) ha (fun w => h (1 - w)) hhc
    (by simp [hh1])
  refine ⟨(fun w => g (1 - w)), hgc, ?_⟩
  have ht : Tendsto (fun w : ℂ => 1 - w) (𝓝[Complex.slitPlane] 0)
      (𝓝[oneSlit] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using htrans.continuousAt.tendsto.mono_left
        (show 𝓝[Complex.slitPlane] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simpa [oneSlit] using hw
  have heq' : (fun z : ℂ => (1 - z) ^ (1 - δ) * h z) =ᶠ[𝓝[oneSlit] 1] g := heq
  simpa [Function.comp_def] using heq'.comp_tendsto ht

/-- An analytic endpoint solution cannot have a nonzero singular connection
coefficient. The identity is imposed only on a slit approach germ. -/
theorem analytic_connection_singular_coefficient_zero (δ : ℂ)
    (hδ : ∀ m : ℤ, δ ≠ (m : ℂ)) (h y u : ℂ → ℂ)
    (hh : AnalyticAt ℂ h 1) (hh1 : h 1 = 1)
    (hy : AnalyticAt ℂ y 1) (hu : AnalyticAt ℂ u 1)
    (d₁ d₂ : ℂ)
    (heq : y =ᶠ[𝓝[oneSlit] 1]
      (fun z => d₁ * u z + d₂ * ((1 - z) ^ (1 - δ) * h z))) :
    d₂ = 0 := by
  let R := Gcoy.AnalyticBridge.regularGerms oneSlit 1
  apply Gcoy.AnalyticBridge.scalar_eq_zero_of_smul_mem R
    (singular_not_regularGerms δ hδ h hh hh1)
  have hr : (fun z => y z - d₁ * u z) ∈ R :=
    Gcoy.AnalyticBridge.mem_regularGerms_of_analytic
      (hy.sub (analyticAt_const.mul hu))
  apply Gcoy.AnalyticBridge.mem_regularGerms_congr (hf := hr)
  filter_upwards [heq] with z hz
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination hz

end Gcoy.SingularGerm

#print axioms Gcoy.SingularGerm.analytic_euler_exponent_nat
#print axioms Gcoy.SingularGerm.cpow_euler
#print axioms Gcoy.SingularGerm.cpow_not_regularGerms
#print axioms Gcoy.SingularGerm.cpow_mul_not_regularGerms
#print axioms Gcoy.SingularGerm.singular_not_regularGerms
#print axioms Gcoy.SingularGerm.analytic_connection_singular_coefficient_zero
