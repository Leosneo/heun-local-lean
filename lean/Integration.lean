import HeunProblem
import FiniteRoot
import AnalyticBridge
import Mathlib.Analysis.Analytic.Constructions

noncomputable section
open scoped Topology ContDiff BigOperators
open Filter

namespace Heun

theorem coefficientPair_analytic (f : Family) (p : Parameters) (N : ℕ)
    (u : ℂ × ℂ) :
    AnalyticAt ℂ (fun v : ℂ × ℂ => coefficientPair f p v.2 v.1 N) u := by
  induction N with
  | zero => exact analyticAt_const
  | succ N ih =>
    simp only [coefficientPair]
    have h₁ := analyticAt_fst.comp ih
    have h₂ := analyticAt_snd.comp ih
    apply h₂.prod
    have ha : AnalyticAt ℂ (fun v : ℂ × ℂ =>
        (v.2 + D p N + v.1 * E f p N) *
          (coefficientPair f p v.2 v.1 N).2 -
        v.1 * F f p N * (coefficientPair f p v.2 v.1 N).1) u := by
      exact (((analyticAt_snd.add analyticAt_const).add
        (analyticAt_fst.mul analyticAt_const)).mul h₂).sub
        ((analyticAt_fst.mul analyticAt_const).mul h₁)
    simpa [div_eq_mul_inv] using ha.mul (analyticAt_const (v :=
      ((((N : ℂ) + 1) * ((N : ℂ) + p.gamma))⁻¹)))

theorem coefficient_analytic (f : Family) (p : Parameters) (N : ℕ)
    (u : ℂ × ℂ) :
    AnalyticAt ℂ (fun v : ℂ × ℂ => coefficient f p v.2 v.1 N) u :=
  analyticAt_snd.comp (coefficientPair_analytic f p N u)

theorem finite_root_germ_exists (f : Family) (p : Parameters)
    (hp : Admissible f p) (k N : ℕ) (hk : k < N) :
    ∃ b : ℂ → ℂ, IsFiniteRootGerm f p k N b := by
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
  let H : ℂ × ℂ → ℂ := fun v => coefficient f p v.2 v.1 N
  let u : ℂ × ℂ := (0, -D p k)
  have hH : AnalyticAt ℂ H u := coefficient_analytic f p N u
  have hpart : fderiv ℂ H u ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ a := by
    have hc := hH.differentiableAt.hasFDerivAt.comp (-D p k)
      (hasFDerivAt_prodMk_right (𝕜 := ℂ) (0 : ℂ) (-D p k))
    exact hc.unique hd.hasFDerivAt
  have hinv : (fderiv ℂ H u ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    rw [hpart]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℂ a⁻¹)
    · ext
      simp [ContinuousLinearMap.toSpanSingleton_apply, ha]
    · ext
      simp [ContinuousLinearMap.toSpanSingleton_apply, ha]
  obtain ⟨b, hb, hbase, heq⟩ :=
    Gcoy.AnalyticBridge.exists_analytic_implicit_branch hH hinv
  refine ⟨b, hb, hbase, ?_⟩
  have ht : Tendsto (fun s : ℂ => (s, b s)) (𝓝 0) (𝓝 u) := by
    have hb0 : b 0 = -D p k := hbase
    simpa [u, hb0] using (continuousAt_id.prodMk hb.continuousAt).tendsto
  have he := ht.eventually heq
  filter_upwards [he] with s hs
  have h := hs.mpr rfl
  simpa [H, u, coefficient_base_root f p hk] using h

end Heun

#print axioms Heun.finite_root_germ_exists
