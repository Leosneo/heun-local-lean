import HeunProblem
import Mathlib.Analysis.Analytic.Order

noncomputable section
open scoped Topology
open Filter

namespace Heun

/-- A homogeneous second-order analytic ODE has no nonzero analytic germ whose
value and first derivative both vanish at an ordinary point. -/
theorem analytic_second_order_zero {y a b : ℂ → ℂ} {c : ℂ}
    (hy : AnalyticAt ℂ y c) (ha : AnalyticAt ℂ a c) (hb : AnalyticAt ℂ b c)
    (hy0 : y c = 0) (hy1 : deriv y c = 0)
    (hode : ∀ᶠ z in 𝓝 c, deriv (deriv y) z + a z * deriv y z + b z * y z = 0) :
    y =ᶠ[𝓝 c] 0 := by
  by_contra hne
  have htop : analyticOrderAt y c ≠ ⊤ :=
    fun h => hne (analyticOrderAt_eq_top.mp h)
  let N := analyticOrderNatAt y c
  have hNorder : analyticOrderAt y c = (N : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt htop).symm
  have htwo : (2 : ℕ∞) ≤ analyticOrderAt y c := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hy).mpr
    intro i hi
    interval_cases i <;> simp [hy0, hy1]
  have hN : 2 ≤ N := by
    rw [hNorder] at htwo
    exact_mod_cast htwo
  let n := N - 2
  have hNn : N = n + 2 := by dsimp [n]; omega
  have horder : analyticOrderAt y c = ((n + 2 : ℕ) : ℕ∞) := by
    rw [hNorder, hNn]
  have hfirst : analyticOrderAt (deriv y) c = ((n + 1 : ℕ) : ℕ∞) := by
    apply analyticOrderAt_deriv_of_pos hy
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, add_assoc] using horder
  have hsecond : analyticOrderAt (deriv (deriv y)) c = (n : ℕ∞) := by
    apply analyticOrderAt_deriv_of_pos hy.deriv
    simpa only [Nat.cast_add, Nat.cast_one] using hfirst
  have hrest : ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (a * deriv y + b * y) c := by
    apply le_trans (le_min _ _) le_analyticOrderAt_add
    · rw [analyticOrderAt_mul ha hy.deriv, hfirst]
      exact le_add_of_nonneg_left (zero_le _)
    · rw [analyticOrderAt_mul hb hy, horder]
      exact (show ((n + 1 : ℕ) : ℕ∞) ≤ ((n + 2 : ℕ) : ℕ∞) by
        exact_mod_cast (show n + 1 ≤ n + 2 by omega)).trans
          (le_add_of_nonneg_left (zero_le _))
  have heq : deriv (deriv y) =ᶠ[𝓝 c] -(a * deriv y + b * y) := by
    filter_upwards [hode] with z hz
    simp only [Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
    linear_combination hz
  have ho := analyticOrderAt_congr heq
  rw [analyticOrderAt_neg, hsecond] at ho
  rw [← ho] at hrest
  have hnfalse : n + 1 ≤ n := by exact_mod_cast hrest
  omega

/-- Equality of value and first derivative uniquely determines an analytic
solution germ of a second-order linear ODE at an ordinary point. -/
theorem analytic_second_order_unique {y v a b : ℂ → ℂ} {c : ℂ}
    (hy : AnalyticAt ℂ y c) (hv : AnalyticAt ℂ v c)
    (ha : AnalyticAt ℂ a c) (hb : AnalyticAt ℂ b c)
    (h0 : y c = v c) (h1 : deriv y c = deriv v c)
    (hyode : ∀ᶠ z in 𝓝 c, deriv (deriv y) z + a z * deriv y z + b z * y z = 0)
    (hvode : ∀ᶠ z in 𝓝 c, deriv (deriv v) z + a z * deriv v z + b z * v z = 0) :
    y =ᶠ[𝓝 c] v := by
  have hd : deriv (y - v) =ᶠ[𝓝 c] deriv y - deriv v := by
    filter_upwards [hy.eventually_analyticAt, hv.eventually_analyticAt] with z hyz hvz
    exact deriv_sub hyz.differentiableAt hvz.differentiableAt
  have hdd := hd.deriv
  have hzero := analytic_second_order_zero (hy.sub hv) ha hb
    (by simpa using sub_eq_zero.mpr h0)
    (by rw [deriv_sub hy.differentiableAt hv.differentiableAt, h1, sub_self])
  have hode : ∀ᶠ z in 𝓝 c, deriv (deriv (y-v)) z +
      a z * deriv (y-v) z + b z * (y-v) z = 0 := by
    filter_upwards [hyode, hvode, hd, hdd, hy.deriv.eventually_analyticAt,
      hv.deriv.eventually_analyticAt] with z hyz hvz hdz hddz hy'z hv'z
    rw [hddz, deriv_sub hy'z.differentiableAt hv'z.differentiableAt, hdz]
    simp only [Pi.sub_apply]
    linear_combination hyz - hvz
  have h := hzero hode
  filter_upwards [h] with z hz
  exact sub_eq_zero.mp hz

theorem analytic_second_order_unique_on {y v a b : ℂ → ℂ} {c : ℂ} {U : Set ℂ}
    (hy : AnalyticOnNhd ℂ y U) (hv : AnalyticOnNhd ℂ v U)
    (hU : IsPreconnected U) (hc : c ∈ U)
    (ha : AnalyticAt ℂ a c) (hb : AnalyticAt ℂ b c)
    (h0 : y c = v c) (h1 : deriv y c = deriv v c)
    (hyode : ∀ᶠ z in 𝓝 c, deriv (deriv y) z + a z * deriv y z + b z * y z = 0)
    (hvode : ∀ᶠ z in 𝓝 c, deriv (deriv v) z + a z * deriv v z + b z * v z = 0) :
    Set.EqOn y v U :=
  hy.eqOn_of_preconnected_of_eventuallyEq hv hU hc
    (analytic_second_order_unique (hy c hc) (hv c hc) ha hb h0 h1 hyode hvode)

theorem analytic_second_order_linear_combination {u v a b : ℂ → ℂ} {c : ℂ}
    (hu : AnalyticAt ℂ u c) (hv : AnalyticAt ℂ v c) (d₁ d₂ : ℂ)
    (huode : ∀ᶠ z in 𝓝 c, deriv (deriv u) z + a z * deriv u z + b z * u z = 0)
    (hvode : ∀ᶠ z in 𝓝 c, deriv (deriv v) z + a z * deriv v z + b z * v z = 0) :
    let w := fun z => d₁ * u z + d₂ * v z
    (∀ᶠ z in 𝓝 c, deriv w z = d₁ * deriv u z + d₂ * deriv v z) ∧
    (∀ᶠ z in 𝓝 c, deriv (deriv w) z + a z * deriv w z + b z * w z = 0) := by
  dsimp only
  have hd : deriv (fun z => d₁ * u z + d₂ * v z) =ᶠ[𝓝 c]
      (fun z => d₁ * deriv u z + d₂ * deriv v z) := by
    filter_upwards [hu.eventually_analyticAt, hv.eventually_analyticAt] with z huz hvz
    exact ((huz.differentiableAt.hasDerivAt.const_mul d₁).add
      (hvz.differentiableAt.hasDerivAt.const_mul d₂)).deriv
  refine ⟨hd, ?_⟩
  filter_upwards [hd, hd.deriv, hu.deriv.eventually_analyticAt,
    hv.deriv.eventually_analyticAt, huode, hvode] with z hdz hddz hu'z hv'z huz hvz
  have hsecond := ((hu'z.differentiableAt.hasDerivAt.const_mul d₁).add
    (hv'z.differentiableAt.hasDerivAt.const_mul d₂)).deriv
  have hsecond' : deriv (fun z => d₁ * deriv u z + d₂ * deriv v z) z =
      d₁ * deriv (deriv u) z + d₂ * deriv (deriv v) z := hsecond
  rw [hddz, hsecond', hdz]
  linear_combination d₁ * huz + d₂ * hvz

/-- A pair with nonzero ordinary-point Wronskian spans every analytic solution
on a connected common domain. This constructs the actual connection identity. -/
theorem analytic_second_order_span {y u v a b : ℂ → ℂ} {c : ℂ} {U : Set ℂ}
    (hy : AnalyticOnNhd ℂ y U) (hu : AnalyticOnNhd ℂ u U)
    (hv : AnalyticOnNhd ℂ v U) (hU : IsPreconnected U) (hc : c ∈ U)
    (ha : AnalyticAt ℂ a c) (hb : AnalyticAt ℂ b c)
    (hyode : ∀ᶠ z in 𝓝 c, deriv (deriv y) z + a z * deriv y z + b z * y z = 0)
    (huode : ∀ᶠ z in 𝓝 c, deriv (deriv u) z + a z * deriv u z + b z * u z = 0)
    (hvode : ∀ᶠ z in 𝓝 c, deriv (deriv v) z + a z * deriv v z + b z * v z = 0)
    (hW : u c * deriv v c - deriv u c * v c ≠ 0) :
    ∃ d₁ d₂ : ℂ, Set.EqOn y (fun z => d₁ * u z + d₂ * v z) U := by
  let W := u c * deriv v c - deriv u c * v c
  let d₁ := (y c * deriv v c - deriv y c * v c) / W
  let d₂ := (u c * deriv y c - deriv u c * y c) / W
  have hd := analytic_second_order_linear_combination (hu c hc) (hv c hc)
    d₁ d₂ huode hvode
  have hw : AnalyticOnNhd ℂ (fun z => d₁ * u z + d₂ * v z) U :=
    fun z hz => (analyticAt_const.mul (hu z hz)).add
      (analyticAt_const.mul (hv z hz))
  refine ⟨d₁, d₂, ?_⟩
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

end Heun

#print axioms Heun.analytic_second_order_zero
#print axioms Heun.analytic_second_order_unique
#print axioms Heun.analytic_second_order_span
