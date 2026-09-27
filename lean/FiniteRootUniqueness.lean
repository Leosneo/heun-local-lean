import Integration
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Uniqueness of the finite roots as analytic germs

The simple-root condition below is proved from the actual finite Heun
coefficient. No existence or uniqueness of a connection-coefficient root
is assumed.
-/

noncomputable section
open scoped Topology BigOperators
open Filter

namespace Heun

/-- The accessory-parameter derivative of the actual coefficient is
invertible at each unperturbed finite root. -/
theorem coefficient_partial_invertible (f : Family) (p : Parameters)
    (hp : Admissible f p) (k N : ℕ) (hk : k < N) :
    (fderiv ℂ (fun v : ℂ × ℂ => coefficient f p v.2 v.1 N) (0, -D p k)
      ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
  let den : ℂ := ∏ m ∈ Finset.range N,
    (((m : ℂ) + 1) * ((m : ℂ) + p.gamma))
  let a : ℂ := (∏ m ∈ (Finset.range N).erase k, (D p m - D p k)) / den
  have hden : den ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact recurrence_denominator_ne_zero hp m
  have ha : a ≠ 0 := by
    apply div_ne_zero _ hden
    apply Finset.prod_ne_zero_iff.mpr
    intro m hm
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hm).1 (D_injective hp h))
  have hd : HasDerivAt (fun B : ℂ => coefficient f p B 0 N) a (-D p k) := by
    simpa only [coefficient_at_s_zero] using
      MoriTakemura.complex_scaled_product_hasDerivAt
        (Finset.range N) (D p) (Finset.mem_range.mpr hk) den
  have hH := coefficient_analytic f p N (0, -D p k)
  have hpart : fderiv ℂ (fun v : ℂ × ℂ => coefficient f p v.2 v.1 N)
      (0, -D p k) ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ a := by
    have hc := hH.differentiableAt.hasFDerivAt.comp (-D p k)
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) (0 : ℂ) (-D p k))
    exact hc.unique hd.hasFDerivAt
  rw [hpart]
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℂ a⁻¹)
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, ha]
  · ext
    simp [ContinuousLinearMap.toSpanSingleton_apply, ha]

/-- Two normalized analytic branches of the same finite root agree as germs. -/
theorem finite_root_germ_unique (f : Family) (p : Parameters)
    (hp : Admissible f p) (k N : ℕ) (hk : k < N)
    {b c : ℂ → ℂ}
    (hb : IsFiniteRootGerm f p k N b)
    (hc : IsFiniteRootGerm f p k N c) :
    b =ᶠ[𝓝 (0 : ℂ)] c := by
  let H : ℂ × ℂ → ℂ := fun v => coefficient f p v.2 v.1 N
  let u : ℂ × ℂ := (0, -D p k)
  have hH : AnalyticAt ℂ H u := coefficient_analytic f p N u
  have hi : (fderiv ℂ H u ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible :=
    coefficient_partial_invertible f p hp k N hk
  obtain ⟨g, hg, hbase, heq⟩ :=
    Gcoy.AnalyticBridge.exists_analytic_implicit_branch hH hi
  have hbranch : ∀ d : ℂ → ℂ, IsFiniteRootGerm f p k N d →
      g =ᶠ[𝓝 (0 : ℂ)] d := by
    intro d hd
    obtain ⟨hdanalytic, hd0, hdroot⟩ := hd
    have ht : Tendsto (fun s : ℂ => (s, d s)) (𝓝 0) (𝓝 u) := by
      simpa [u, hd0] using
        (continuousAt_id.prodMk hdanalytic.continuousAt).tendsto
    have he := ht.eventually heq
    filter_upwards [he, hdroot] with s hs hroot
    apply hs.mp
    simpa [H, u, coefficient_base_root f p hk] using hroot
  exact (hbranch b hb).symm.trans (hbranch c hc)

/-- Existence with uniqueness in the germ sense, rather than false global
uniqueness of functions that may be changed away from zero. -/
theorem finite_root_germ_exists_unique (f : Family) (p : Parameters)
    (hp : Admissible f p) (k N : ℕ) (hk : k < N) :
    ∃ b : ℂ → ℂ, IsFiniteRootGerm f p k N b ∧
      ∀ c : ℂ → ℂ, IsFiniteRootGerm f p k N c → b =ᶠ[𝓝 (0 : ℂ)] c := by
  obtain ⟨b, hb⟩ := finite_root_germ_exists f p hp k N hk
  exact ⟨b, hb, fun c hc => finite_root_germ_unique f p hp k N hk hb hc⟩

/-- Finite-root Taylor coefficients are independent of the representative
chosen for the normalized analytic root germ. -/
theorem finite_root_derivatives_unique (f : Family) (p : Parameters)
    (hp : Admissible f p) (k N j : ℕ) (hk : k < N)
    {b c : ℂ → ℂ}
    (hb : IsFiniteRootGerm f p k N b)
    (hc : IsFiniteRootGerm f p k N c) :
    iteratedDeriv j b 0 = iteratedDeriv j c 0 := by
  exact Filter.EventuallyEq.iteratedDeriv_eq j
    (finite_root_germ_unique f p hp k N hk hb hc)

end Heun

#print axioms Heun.finite_root_germ_unique
#print axioms Heun.finite_root_germ_exists_unique
